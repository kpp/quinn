use std::sync::{Arc, Mutex};
use std::task::{Context, Waker};

use slab::Slab;

/// Broadcasts an event to any number of waiters
#[derive(Clone)]
pub struct NotifyOwned {
    shared: Arc<Mutex<Shared>>,
}

struct Shared {
    version: u64,
    wakers: Slab<Waker>,
}

impl NotifyOwned {
    pub fn new() -> Self {
        Self {
            shared: Arc::new(Mutex::new(Shared {
                version: 0,
                wakers: Slab::new(),
            })),
        }
    }

    pub fn notify_all(&self) {
        let mut shared = self.shared.lock().unwrap();
        shared.version = shared.version.wrapping_add(1);
        let n = shared.wakers.len();
        for waker in shared.wakers.drain() {
            waker.wake();
        }
        // Limit unused slots, which cost iteration time as well as memory
        if n * 4 < shared.wakers.capacity() {
            shared.wakers = Slab::with_capacity(n);
        }
    }

    pub fn wait(&self) -> Waiter {
        Waiter {
            shared: self.shared.clone(),
            state: None,
        }
    }
}

pub struct Waiter {
    shared: Arc<Mutex<Shared>>,
    state: Option<State>,
}

impl Waiter {
    /// Register to be woken by the next `notify_all`. Must be called before readiness could occur,
    /// e.g. inside a lock guarding the state of interest.
    pub fn register(&mut self, ctx: &mut Context<'_>) {
        let mut shared = self.shared.lock().unwrap();
        match self.state {
            None => {
                self.state = Some(State {
                    version: shared.version,
                    index: shared.wakers.insert(ctx.waker().clone()),
                });
            }
            Some(State { version, index }) => {
                debug_assert!(shared.version == version);
                shared.wakers[index] = ctx.waker().clone();
            }
        }
    }
}

impl Drop for Waiter {
    fn drop(&mut self) {
        if let Some(State { index, version }) = self.state {
            if let Ok(mut shared) = self.shared.lock() {
                // Ensure `wakers` doesn't grow if `Waiter`s are repeatedly constructed and dropped
                if shared.version == version {
                    shared.wakers.remove(index);
                }
            }
        }
    }
}

struct State {
    version: u64,
    index: usize,
}
