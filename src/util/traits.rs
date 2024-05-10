pub trait Recurse {
    type ArgType;

    fn recurse<T>(&self, ctx: &mut T, f: fn(ctx: &mut T, expr: &Self::ArgType) -> bool);
}
