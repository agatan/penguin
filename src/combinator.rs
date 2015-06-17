//! Parser combinators are defined here.
//! Using them, you can make a new parser of some primitive parsers.
//! Parsers made of some primitive parsers are also parser,
//! so you can combine them with any other parsers.

use primitives::*;

use std::iter::{Iterator, Peekable};

#[derive(Debug, Clone)]
/// Map a return value of the parser with the function.
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

/// map a return value of the parser with the function.
pub fn map<B, P: Parser, F>(p: P, f: F) -> Map<P, F>
where F: FnMut(P::Output) -> B {
    Map { p: p, f: f }
}

#[test]
fn map_test() {
    let mut m = map(exact('a'), |r| { format!("matched: {}", r) });
    let src = "abc".chars().peekable();
    let res = m.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!("matched: a".to_string(), r);
        assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
    }
}
