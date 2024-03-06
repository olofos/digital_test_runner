use rand::{rngs::StdRng, SeedableRng};

#[derive(Debug)]
pub(crate) struct EvalContext {
    values: Vec<(String, i64)>,
    frame_stack: Vec<usize>,
    pub rng: StdRng,
    seed: u64,
}

impl EvalContext {
    pub fn new() -> Self {
        let mut seed_bytes: [u8; 8] = Default::default();
        getrandom::getrandom(&mut seed_bytes).unwrap();
        let seed = u64::from_le_bytes(seed_bytes);

        Self {
            values: vec![],
            frame_stack: vec![],
            rng: StdRng::seed_from_u64(seed),
            seed,
        }
    }

    pub fn with_seed(seed: u64) -> Self {
        Self {
            values: vec![],
            frame_stack: vec![],
            rng: StdRng::seed_from_u64(seed),
            seed,
        }
    }

    pub fn push_frame(&mut self) {
        self.frame_stack.push(self.values.len())
    }

    pub fn pop_frame(&mut self) {
        let len = self.frame_stack.pop().unwrap_or(0);
        self.values.truncate(len);
    }

    pub fn set(&mut self, name: &str, value: i64) {
        let frame_start = *self.frame_stack.last().unwrap_or(&0);
        if let Some((_, entry_value)) = self.values[frame_start..]
            .iter_mut()
            .find(|entry| entry.0 == name)
        {
            *entry_value = value;
        } else {
            self.values.push((name.to_owned(), value));
        }
    }

    pub fn get(&self, name: &str) -> Option<i64> {
        self.values
            .iter()
            .rev()
            .find(|entry| entry.0 == name)
            .map(|entry| entry.1)
    }

    pub fn reset_random_seed(&mut self) {
        self.rng = StdRng::seed_from_u64(self.seed);
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
}
