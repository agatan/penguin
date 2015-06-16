use primitives::*;

use std::iter::{Iterator, Peekable};

pub struct Map<P, F> {
    p: P,
    f: F,
}
impl <B, F, In: Clone, P: Parser<Input=In>> Parser for Map<P, F>
where F: FnMut(P::Output) -> B {
    type Output = B;
    type Input = In;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        self.p.parse(src)
            .map(|(a, ctx)| ((self.f)(a), ctx))
    }
}

pub fn map<B, P: Parser + Clone, F>(p: &P, f: F) -> Map<P, F>
where F: FnMut(P::Output) -> B {
    Map { p: p.clone(), f: f }
}

#[test]
fn map_test() {
    let mut m = map(&exact('a'), |_| { 1 });
    let src = "abc".chars().peekable();
    let res = m.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!(1, r);
        assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
    }
}
