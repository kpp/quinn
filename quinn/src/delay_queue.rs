use std::{fmt, ops::RangeInclusive};

use slab::Slab;

/// Stores values to be yielded at specific times in the future
#[derive(Debug)]
pub struct DelayQueue<T> {
    /// Definitions of each active timer
    timers: Slab<TimerState<T>>,

    /// Hierarchical timer wheel
    ///
    /// Timers are bucketed into slots organized into levels. Level n spans 2^(`LOG_2_SLOTS` *
    /// (n+1)) ticks, and each of its slots corresponds to a span of 2^(`LOG_2_SLOTS` * n). The
    /// expiry time of the first slot in each level is always a multiple of the level's size. When
    /// the expiry time of a slot in a level above 0 is reached, timers stored in that slot are
    /// redistributed to lower levels. When the last slot in a level expires, the level advances to
    /// cover the next span of ticks.
    ///
    /// Timers always use the lowest possible level. Every level above 0 has an empty slot,
    /// corresponding exactly to the span of the previous level.
    ///
    /// The set of timers in a slot is an intrusive doubly-linked list, allowing constant-time
    /// insertion and removal.
    levels: [Level; LEVELS],

    /// Earliest point at which a timer may be pending
    ///
    /// Each `LOG_2_SLOTS` bits of this are a cursor into the associated level, in order of
    /// ascending significance.
    next_tick: u64,
}

impl<T> DelayQueue<T> {
    /// Create an empty queue starting at time `0`
    pub fn new() -> Self {
        Self {
            timers: Slab::new(),
            levels: [Level::new(); LEVELS],
            next_tick: 0,
        }
    }

    /// Returns a timer that has expired by `now`, if any
    ///
    /// `now` must be at least the largest previously passed value
    pub fn poll(&mut self, now: u64) -> Option<T>
    where
        T: fmt::Debug,
    {
        debug_assert!(now >= self.next_tick, "time advances monotonically");
        loop {
            // Advance towards the next timeout
            self.advance_towards(now);
            // Check for timeouts in the immediate future
            if let Some(value) = self.scan_bottom(now) {
                return Some(value);
            }
            // If we can't advance any further, bail out
            if self.next_tick >= now {
                return None;
            }
        }
    }

    /// Find a timer expired by `now` in level 0
    fn scan_bottom(&mut self, now: u64) -> Option<T> {
        for slot in &mut self.levels[0].slots[range_in_level(0, self.next_tick..=now)] {
            if let Some(timer) = slot.take() {
                let state = self.timers.remove(timer.0);
                debug_assert_eq!(state.prev, None, "head of list has no predecessor");
                if let Some(next) = state.next {
                    debug_assert_eq!(
                        self.timers[next.0].prev,
                        Some(timer),
                        "successor links to head"
                    );
                    self.timers[next.0].prev = None;
                }
                *slot = state.next;
                self.next_tick = state.expiry;
                return Some(state.value);
            }
        }
        None
    }

    /// Advance to the start of the first nonempty slot or `now`, whichever is sooner
    fn advance_towards(&mut self, now: u64) {
        for level in 0..LEVELS {
            for slot in range_in_level(level, self.next_tick..=now) {
                debug_assert!(
                    now >= slot_start(self.next_tick, level, slot),
                    "slot overlaps with the past"
                );
                if self.levels[level].slots[slot].is_some() {
                    self.advance_to(level, slot);
                    return;
                }
            }
        }
        self.next_tick = now;
    }

    /// Advance to a specific slot, which must be the first nonempty slot
    fn advance_to(&mut self, level: usize, slot: usize) {
        debug_assert!(
            self.levels[..level]
                .iter()
                .all(|level| level.slots.iter().all(|x| x.is_none())),
            "lower levels are empty"
        );
        debug_assert!(
            self.levels[level].slots[..slot].iter().all(Option::is_none),
            "lower slots in this level are empty"
        );

        // Advance into the slot
        self.next_tick = slot_start(self.next_tick, level, slot);

        // Drain it into the lower levels, if possible
        if level > 0 {
            while let Some(timer) = self.levels[level].slots[slot].take() {
                let next = self.timers[timer.0].next;
                self.levels[level].slots[slot] = next;
                if let Some(next) = next {
                    self.timers[next.0].prev = None;
                }
                self.list_unlink(timer);
                self.schedule(timer);
            }
        }
    }

    /// Link `timer` from the slot associated with its expiry
    fn schedule(&mut self, timer: Timer) {
        debug_assert_eq!(
            self.timers[timer.0].next, None,
            "timer isn't already scheduled"
        );
        debug_assert_eq!(
            self.timers[timer.0].prev, None,
            "timer isn't already scheduled"
        );
        let (level, slot) = timer_index(self.next_tick, self.timers[timer.0].expiry);
        // Insert `timer` at the head of the list in the target slot
        let head = self.levels[level].slots[slot];
        self.timers[timer.0].next = head;
        if let Some(head) = head {
            self.timers[head.0].prev = Some(timer);
        }
        self.levels[level].slots[slot] = Some(timer);
    }

    /// Lower bound on when the next timer will expire, if any
    pub fn next_timeout(&self) -> Option<u64> {
        for level in 0..LEVELS {
            let start = ((self.next_tick >> (level * LOG_2_SLOTS)) & (SLOTS - 1) as u64) as usize;
            for slot in start..SLOTS {
                if self.levels[level].slots[slot].is_some() {
                    return Some(slot_start(self.next_tick, level, slot));
                }
            }
        }
        None
    }

    /// Register a timer that will yield `value` at `timeout`
    pub fn insert(&mut self, timeout: u64, value: T) -> Timer {
        let timer = Timer(self.timers.insert(TimerState {
            expiry: timeout.max(self.next_tick),
            prev: None,
            next: None,
            value,
        }));
        self.schedule(timer);
        timer
    }

    /// Adjust `timer` to expire at `timeout`
    pub fn reset(&mut self, timer: Timer, timeout: u64) {
        self.unlink(timer);
        self.timers[timer.0].expiry = timeout.max(self.next_tick);
        self.schedule(timer);
    }

    /// Cancel `timer`
    #[cfg(test)]
    pub fn remove(&mut self, timer: Timer) -> T {
        self.unlink(timer);
        self.timers.remove(timer.0).value
    }

    /// Remove all references to `timer`
    fn unlink(&mut self, timer: Timer) {
        let (level, slot) = timer_index(self.next_tick, self.timers[timer.0].expiry);
        let link = self.levels[level].slots[slot].unwrap();
        if link == timer {
            // Remove reference from slot
            self.levels[level].slots[slot] = self.timers[link.0].next;
            debug_assert_eq!(
                self.timers[timer.0].prev, None,
                "head of list has no predecessor"
            );
        }
        self.list_unlink(timer);
    }

    /// Remove `timer` from its list
    fn list_unlink(&mut self, timer: Timer) {
        if let Some(prev) = self.timers[timer.0].prev.take() {
            // Remove reference from predecessor
            self.timers[prev.0].next = self.timers[timer.0].next;
        }
        if let Some(next) = self.timers[timer.0].next.take() {
            // Remove reference from successor
            self.timers[next.0].prev = self.timers[timer.0].prev;
        }
    }
}

fn range_in_level(level: usize, raw: RangeInclusive<u64>) -> RangeInclusive<usize> {
    let shift = level * LOG_2_SLOTS;
    const MASK: u64 = SLOTS as u64 - 1;
    let start = ((*raw.start() >> shift) & MASK) as usize;
    let level_end = (*raw.start() >> shift) | MASK;
    let end = ((*raw.end() >> shift).min(level_end) & MASK) as usize;
    start..=end
}

/// Compute the first tick that lies within a slot
fn slot_start(base: u64, level: usize, slot: usize) -> u64 {
    let shift = (level * LOG_2_SLOTS) as u64;
    (base & ((!0 << shift) << LOG_2_SLOTS as u64)) | ((slot as u64) << shift)
}

/// Compute the level and slot for a certain expiry
fn timer_index(base: u64, expiry: u64) -> (usize, usize) {
    let differing_bits = base ^ expiry;
    let level = (63 - (differing_bits | 1).leading_zeros()) as usize / LOG_2_SLOTS;
    debug_assert!(level < LEVELS, "every possible expiry is in range");
    let slot_base = (base >> (level * LOG_2_SLOTS)) & (!0 << LOG_2_SLOTS);
    let slot = (expiry >> (level * LOG_2_SLOTS)) - slot_base;
    debug_assert!(slot < SLOTS as u64);
    (level, slot as usize)
}

impl<T> Default for DelayQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
struct TimerState<T> {
    /// Lowest argument to `poll` for which this timer may be returned
    expiry: u64,
    /// Value returned to the caller on expiry
    value: T,
    /// Predecessor within a slot's list
    prev: Option<Timer>,
    /// Successor within a slot's list
    next: Option<Timer>,
}

/// A set of contiguous timer lists, ordered by expiry
#[derive(Copy, Clone)]
struct Level {
    slots: [Option<Timer>; SLOTS],
}

impl Level {
    fn new() -> Self {
        Self {
            slots: [None; SLOTS],
        }
    }
}

impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut m = f.debug_map();
        for (i, Timer(t)) in self
            .slots
            .iter()
            .enumerate()
            .filter_map(|(i, x)| x.map(|t| (i, t)))
        {
            m.entry(&i, &t);
        }
        m.finish()
    }
}

const LEVELS: usize = 11;
const LOG_2_SLOTS: usize = 6;
const SLOTS: usize = 1 << LOG_2_SLOTS;

// Future work: add a niche here
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Timer(usize);

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn max_timeout() {
        let mut queue = DelayQueue::new();
        queue.insert(u64::MAX, ());
        assert!(queue.poll(u64::MAX - 1).is_none());
        assert!(queue.poll(u64::MAX).is_some());
    }

    #[test]
    fn level_ranges() {
        assert_eq!(range_in_level(0, 0..=1), 0..=1);
        assert_eq!(range_in_level(0, 0..=SLOTS as u64), 0..=SLOTS - 1);
        assert_eq!(range_in_level(1, 0..=SLOTS as u64), 0..=1);
        assert_eq!(range_in_level(1, 0..=(SLOTS as u64).pow(2)), 0..=SLOTS - 1);
        assert_eq!(range_in_level(2, 0..=(SLOTS as u64).pow(2)), 0..=1);
    }

    #[test]
    fn slot_starts() {
        for i in 0..SLOTS {
            assert_eq!(slot_start(0, 0, i), i as u64);
            assert_eq!(slot_start(SLOTS as u64, 0, i), SLOTS as u64 + i as u64);
            assert_eq!(slot_start(SLOTS as u64 + 1, 0, i), SLOTS as u64 + i as u64);
            for j in 1..LEVELS {
                assert_eq!(
                    slot_start(0, j, i),
                    (SLOTS as u64).pow(j as u32).wrapping_mul(i as u64)
                );
            }
        }
    }

    #[test]
    fn indexes() {
        assert_eq!(timer_index(0, 0), (0, 0));
        assert_eq!(timer_index(0, SLOTS as u64 - 1), (0, SLOTS - 1));
        assert_eq!(
            timer_index(SLOTS as u64 - 1, SLOTS as u64 - 1),
            (0, SLOTS - 1)
        );
        assert_eq!(timer_index(0, SLOTS as u64), (1, 1));
        for i in 0..LEVELS {
            assert_eq!(timer_index(0, (SLOTS as u64).pow(i as u32)), (i, 1));
            if i < 10 {
                assert_eq!(
                    timer_index(0, (SLOTS as u64).pow(i as u32 + 1) - 1),
                    (i, SLOTS - 1)
                );
                assert_eq!(
                    timer_index(SLOTS as u64 - 1, (SLOTS as u64).pow(i as u32 + 1) - 1),
                    (i, SLOTS - 1)
                );
            }
        }
    }

    #[test]
    fn next_timeout() {
        let mut queue = DelayQueue::new();
        assert_eq!(queue.next_timeout(), None);
        let k = queue.insert(0, ());
        assert_eq!(queue.next_timeout(), Some(0));
        queue.remove(k);
        assert_eq!(queue.next_timeout(), None);
        queue.insert(1234, ());
        assert!(queue.next_timeout().unwrap() > 12);
        queue.insert(12, ());
        assert_eq!(queue.next_timeout(), Some(12));
    }

    #[test]
    fn poll_boundary() {
        let mut queue = DelayQueue::new();
        queue.insert(SLOTS as u64 - 1, 'a');
        queue.insert(SLOTS as u64, 'b');
        assert_eq!(queue.poll(SLOTS as u64 - 2), None);
        assert_eq!(queue.poll(SLOTS as u64 - 1), Some('a'));
        assert_eq!(queue.poll(SLOTS as u64 - 1), None);
        assert_eq!(queue.poll(SLOTS as u64), Some('b'));
    }

    proptest! {
        #[test]
        fn poll(a in time(), b in time()) {
            if a == b { return Ok(()); }
            let mut queue = DelayQueue::new();
            queue.insert(a, 'a');
            queue.insert(b, 'b');
            let (first, value_first, second, value_second) = match a > b {
                false => (a, 'a', b, 'b'),
                true => (b, 'b', a, 'a'),
            };
            if first > 0 {
                assert_eq!(queue.poll(0), None);
                assert_eq!(queue.poll(first-1), None);
            }
            assert_eq!(queue.poll(first), Some(value_first));
            assert_eq!(queue.poll(second-1), None);
            assert_eq!(queue.poll(second), Some(value_second));
        }

        #[test]
        fn index_start_consistency(a in time(), b in time()) {
            let base = a.min(b);
            let t = a.max(b);
            let (level, slot) = timer_index(base, t);
            let start = slot_start(base, level, slot);
            assert!(start <= t);
            if let Some(end) = start.checked_add((SLOTS as u64).pow(level as u32)) {
                assert!(end > t);
            } else {
                // Slot contains u64::MAX
                assert!(start >= slot_start(0, 10, 15));
                if level == 10 {
                    assert_eq!(slot, 15);
                } else {
                    assert_eq!(slot, SLOTS - 1);
                }
            }
        }
    }

    /// Generates a time whose level/slot is more or less uniformly distributed
    fn time() -> impl Strategy<Value = u64> {
        ((0..LEVELS as u32), (0..SLOTS as u64)).prop_perturb(|(level, mut slot), mut rng| {
            if level == 10 {
                slot = slot.min(15);
            }
            let slot_size = (SLOTS as u64).pow(level);
            let slot_start = slot * slot_size;
            let slot_end = (slot + 1).saturating_mul(slot_size);
            rng.gen_range(slot_start..slot_end)
        })
    }
}
