//! Primitive helpers like optional or many.

use prim::{Parser, ParseResult};
use std::iter::Peekable;

#[derive(Debug, Clone)]
/// A optional parser.
pub struct Optional<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for Optional<In, P> {
    type Output = Option<P::Output>;
    type Input = P::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        match self.p.parse(src) {
            Ok((r, ctx)) => Ok((Some(r), ctx)),
            Err((_, ctx)) => Ok((None, ctx)),
        }
    }
}

/// Make a optional parser. If following tokens are matched the argument parser,
/// it returns `Some(T)`. If not, it just returns `None` and doesn't cosume tokens of the source.
///
/// ```
/// use rparse::prim::{Parser, string, option};
///
/// let str_test = string("tes");
/// let src = "test".chars().peekable();
/// let mut opt = option(str_test);
/// let res = opt.parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!("tes".to_string(), r.unwrap());
///     assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
/// }
///
/// let str_test = string("example");
/// let src = "test".chars().peekable();
/// let mut opt = option(str_test);
/// let res = opt.parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert!(r.is_none());
///     assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn option<I: Clone, P: Parser<Input=I>>(p: P) -> Optional<I, P> {
    Optional { p : p }
}

#[test]
fn option_test() {
    use prim::*;
    let str_test = string("tes");
    let src = "test".chars().peekable();
    let mut opt = option(str_test);
    let res = opt.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!("tes".to_string(), r.unwrap());
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }

    let str_test = string("example");
    let src = "test".chars().peekable();
    let mut opt = option(str_test);
    let res = opt.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert!(r.is_none());
        assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that matches zero or more repeated patterns of the argument parser.
pub struct Many<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for Many<In, P> {
    type Output = Vec<P::Output>;
    type Input = P::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        let mut ret = vec![];
        let mut s = src;

        loop {
            match self.p.parse(s) {
                Ok((r, ctx)) => {
                    s = ctx;
                    ret.push(r);
                },
                Err((_, ctx)) => {
                    return Ok((ret, ctx));
                }
            }
        }
    }
}

/// Make a Many parser. It matches zero or more repeated patterns of the argument parser.
///
/// ```
/// use rparse::prim::{Parser, exact, many};
///
/// let a_ex = exact('a');
/// let src = "aaaabb".chars().peekable();
/// let mut many_p = many(a_ex);
/// let res: Result<(Vec<_>, _), _> = many_p.parse(src);
/// assert!(res.is_ok());
/// if let Ok((v, ctx)) = res {
///     assert_eq!(vec!['a', 'a', 'a', 'a'], v);
///     assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
/// }
/// ```
///
/// Notice that, this can match no repeated pattern.
///
/// ```
/// use rparse::prim::{Parser, exact, many};
///
/// let a_ex = exact('a');
/// let src = "bb".chars().peekable();
/// let mut many_p = many(a_ex);
/// let res: Result<(Vec<_>, _), _> = many_p.parse(src);
/// assert!(res.is_ok());
/// if let Ok((v, ctx)) = res {
///     assert!(v.is_empty());
///     assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn many<I: Clone, P: Parser<Input=I>>(p: P) -> Many<I, P> {
    Many { p: p }
}

#[test]
fn many_test() {
    use prim::*;
    let a_ex = exact('a');
    let src = "aaaabb".chars().peekable();
    let mut many_p = many(a_ex);
    let res: Result<(Vec<_>, _), _> = many_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert_eq!(vec!['a', 'a', 'a', 'a'], v);
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }

    let a_ex = exact('a');
    let src = "bb".chars().peekable();
    let mut many_p = many(a_ex);
    let res: Result<(Vec<_>, _), _> = many_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert!(v.is_empty());
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that matches one or more repeated patterns of the argument parser.
pub struct Many1<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for Many1<In, P> {
    type Output = Vec<P::Output>;
    type Input = P::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        let save = src.clone();
        let mut ret = vec![];
        let mut s = src;

        loop {
            match self.p.parse(s) {
                Ok((r, ctx)) => {
                    s = ctx;
                    ret.push(r);
                },
                Err((e, ctx)) => {
                    if ret.is_empty() {
                        return Err((e, save));
                    }
                    return Ok((ret, ctx));
                }
            }
        }
    }
}

/// Make a Many1 parser. It matches one or more repeated patterns of the argument parser.
///
/// ```
/// use rparse::prim::{Parser, exact, many1};
///
/// let a_ex = exact('a');
/// let src = "aaaabb".chars().peekable();
/// let mut many1_p = many1(a_ex);
/// let res: Result<(Vec<_>, _), _> = many1_p.parse(src);
/// assert!(res.is_ok());
/// if let Ok((v, ctx)) = res {
///     assert_eq!(vec!['a', 'a', 'a', 'a'], v);
///     assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
/// }
/// ```
///
/// Notice that, this parser cannot match no repeated pattern.
///
/// ```
/// use rparse::prim::{Parser, exact, many1};
///
/// let a_ex = exact('a');
/// let src = "bb".chars().peekable();
/// let mut many1_p = many1(a_ex);
/// let res: Result<(Vec<_>, _), _> = many1_p.parse(src);
/// assert!(res.is_err());
/// if let Err((_, ctx)) = res {
///     assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn many1<I: Clone, P: Parser<Input=I>>(p : P) -> Many1<I, P> {
    Many1 { p : p }
}

#[test]
fn many1_parser() {
    use prim::*;
    let a_ex = exact('a');
    let src = "aaaabb".chars().peekable();
    let mut many1_p = many1(a_ex);
    let res: Result<(Vec<_>, _), _> = many1_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert_eq!(vec!['a', 'a', 'a', 'a'], v);
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }

    let a_ex = exact('a');
    let src = "bb".chars().peekable();
    let mut many1_p = many1(a_ex);
    let res: Result<(Vec<_>, _), _> = many1_p.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that matches either parser1 or parser2.
pub struct Select<I, P1, P2>
where I: Clone, P1: Parser<Input=I>, P2: Parser<Input=I, Output=P1::Output> {
    p1: P1,
    p2: P2,
}

impl <In, P1, P2> Parser for Select<In, P1, P2>
where In: Clone, P1: Parser<Input=In>, P2: Parser<Input=In, Output=P1::Output> {
    type Output = P1::Output;
    type Input = In;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        match self.p1.parse(src) {
            Ok((r, ctx)) => Ok((r, ctx)),
            Err((_, ctx)) => self.p2.parse(ctx),
        }
    }
}

/// Make a parser that matches either parser1 or parser2.
///
/// ```
/// use rparse::prim::{Parser, exact, select};
///
/// let a_ex = exact('a');
/// let b_ex = exact('b');
/// let mut select_ab = select(a_ex, b_ex);
/// let src = "bar".chars().peekable();
/// let res = select_ab.parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!('b', r);
///     assert_eq!(vec!['a', 'r'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn select<I, P1, P2>(p1: P1, p2: P2) -> Select<I, P1, P2>
where I: Clone, P1: Parser<Input=I>,
                P2: Parser<Input=I, Output=P1::Output> {
    Select { p1: p1, p2: p2 }
}

#[test]
fn select_test() {
    use prim::*;
    let a_ex = exact('a');
    let b_ex = exact('b');
    let mut sel_ab = select(a_ex, b_ex);
    let src = "abc".chars().peekable();
    let res = sel_ab.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!('a', r);
        assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
    }
    let src = "bac".chars().peekable();
    let res = sel_ab.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!('b', r);
        assert_eq!(vec!['a', 'c'], ctx.collect::<Vec<_>>());
    }

    let src = "cd".chars().peekable();
    let res = sel_ab.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['c', 'd'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that matches a patten of the argument parser and ignores that return value.
pub struct Success<I, P>
where I: Clone, P: Parser<Input=I> {
    p: P,
}
impl <I: Clone, P: Parser<Input=I>> Parser for Success<I, P> {
    type Output = ();
    type Input = I;

    fn parse<In>(&mut self, src: Peekable<In>)
        -> ParseResult<Self::Output, Peekable<In>>
        where In: Clone + Iterator<Item=Self::Input> {
        match self.p.parse(src) {
            Ok((_, ctx)) => Ok(((), ctx)),
            Err(e) => Err(e),
        }
    }
}

/// Make a parser that matches a pattern of the argument parser and ignores that return value.
///
/// ```
/// use rparse::prim::*;
/// use rparse::combinator::*;
///
/// let a_ex = exact('a');
/// let src = "abc".chars().peekable();
/// let res = success(a_ex).parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!((), r);
///     assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn success<I, P>(p: P) -> Success<I, P>
where I: Clone, P: Parser<Input=I> {
    Success { p : p }
}

