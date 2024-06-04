use crate::framed_map::FramedMap;
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::cell::RefCell;

#[derive(Debug)]
pub struct EvalContext {
    vars: FramedMap<String, i64>,
    rng: RefCell<StdRng>,
    seed: u64,
}

#[derive(Debug)]
pub struct EvalContextGuard<'a> {
    ctx: &'a mut EvalContext,
}

impl<'a> std::ops::Deref for EvalContextGuard<'a> {
    type Target = EvalContext;

    fn deref(&self) -> &Self::Target {
        self.ctx
    }
}

impl<'a> std::ops::DerefMut for EvalContextGuard<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.ctx
    }
}

impl<'a> Drop for EvalContextGuard<'a> {
    fn drop(&mut self) {
        self.ctx.pop_frame()
    }
}

impl EvalContext {
    pub fn new() -> Self {
        let mut seed_bytes: [u8; 8] = Default::default();
        getrandom::getrandom(&mut seed_bytes).unwrap();
        let seed = u64::from_le_bytes(seed_bytes);

        Self::with_seed(seed)
    }

    pub fn with_seed(seed: u64) -> Self {
        Self {
            vars: FramedMap::new(),
            rng: RefCell::new(StdRng::seed_from_u64(seed)),
            seed,
        }
    }

    pub fn push_frame(&mut self) {
        self.vars.push_frame()
    }

    pub fn pop_frame(&mut self) {
        self.vars.pop_frame()
    }

    #[allow(dead_code)]
    pub fn new_frame(&mut self) -> EvalContextGuard {
        self.push_frame();
        EvalContextGuard { ctx: self }
    }

    pub fn set(&mut self, name: &str, value: i64) {
        self.vars.set(name, value)
    }

    pub fn get(&self, name: &str) -> Option<i64> {
        self.vars.get(name)
    }

    pub fn reset_random_seed(&mut self) {
        self.rng = RefCell::new(StdRng::seed_from_u64(self.seed));
    }

    pub fn random<R: rand::distributions::uniform::SampleRange<i64>>(&self, range: R) -> i64 {
        self.rng.borrow_mut().gen_range(range)
    }
}

impl Default for EvalContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_context_works() {
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(ctx.get("a"), Some(1));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.set("a", 4);
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));

        ctx.push_frame();
        ctx.set("a", 5);
        ctx.set("b", 6);
        assert_eq!(ctx.get("a"), Some(5));
        assert_eq!(ctx.get("b"), Some(6));
        assert_eq!(ctx.get("c"), Some(3));

        ctx.pop_frame();
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
    }

    #[test]
    fn eval_context_guard_works() {
        let mut ctx = EvalContext::new();

        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(ctx.get("a"), Some(1));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        {
            let mut ctx = ctx.new_frame();
            ctx.set("a", 4);
            assert_eq!(ctx.get("a"), Some(4));
            assert_eq!(ctx.get("b"), Some(2));
            assert_eq!(ctx.get("c"), Some(3));

            {
                let mut ctx = ctx.new_frame();
                ctx.set("c", 5);
                assert_eq!(ctx.get("a"), Some(4));
                assert_eq!(ctx.get("b"), Some(2));
                assert_eq!(ctx.get("c"), Some(5));
            }

            assert_eq!(ctx.get("a"), Some(4));
            assert_eq!(ctx.get("b"), Some(2));
            assert_eq!(ctx.get("c"), Some(3));
        }
        assert_eq!(ctx.get("a"), Some(1));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
    }
}
