//! Parser combinators are defined here.
//! Using them, you can make a new parser of some primitive parsers.
//! Parsers made of some primitive parsers are also parser,
//! so you can combine them with any other parsers.


use prim::*;

use std::iter::{Iterator, Peekable};

/// Parser extension trait. This trait defines some combinator methods.
pub trait AdvancedParser : Parser {
    /// Map the result of this parser with the function `f`.
    ///
    /// ```
    /// use rparse::prim::{Parser, set};
    /// use rparse::combinator::{AdvancedParser};
    ///
    /// let ss = ['a', 'b', 'c'];
    /// let set_parser = set(&ss);
    /// let res = set_parser.map(|c| format!("matched: {}", c))
    ///                            .parse("cat".chars().peekable());
    /// assert!(res.is_ok());
    /// if let Ok((r, _)) = res {
    ///     assert_eq!("matched: c".to_string(), r);
    /// }
    /// ```
    fn map<B, F>(self, f: F) -> Map<Self, F>
        where F: FnMut(Self::Output) -> B;
}

impl <P: Parser> AdvancedParser for P {
    fn map<B, F>(self, f: F) -> Map<Self, F>
    where F: FnMut(Self::Output) -> B {
        Map { p: self, f: f }
    }
}

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
    let ss = vec!['a', 'b', 'c'];
    let set_parser = set(&ss);
    let mut m = set_parser.map(|c| format!("matched: {}", c));
    let src = "abc".chars().peekable();
    let res = m.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!("matched: a".to_string(), r);
        assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that doesn't cosume any token of the source.
/// It only tests the argument parser matches following tokens.
pub struct FollowedBy<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for FollowedBy<In, P> {
    type Output = ();
    type Input = P::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        let save = src.clone();
        match self.p.parse(src) {
            Ok((_, _)) => Ok(((), save)),
            Err((e, _)) => Err((e, save))
        }
    }
}

/// Make a parser that tests the argument parser matches following tokens.
///
/// ```
/// use rparse::prim::{Parser, exact};
/// use rparse::combinator::followed_by;
///
/// let t_ex = exact('t');
/// let src = "test".chars().peekable();
/// let mut and_p = followed_by(t_ex);
/// let res = and_p.parse(src);
/// assert!(res.is_ok());
/// if let Ok(((), ctx)) = res {
///     assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn followed_by<I: Clone, P: Parser<Input=I>>(p: P) -> FollowedBy<I, P> {
    FollowedBy { p : p }
}

#[test]
fn followed_by_test() {
    let t_ex = exact('t');
    let src = "test".chars().peekable();
    let mut and_p = followed_by(t_ex);
    let res = and_p.parse(src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that doesn't consume any token of the source.
/// It only tests the argument parser won't match following tokens.
pub struct NotFollowedBy<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for NotFollowedBy<In, P> {
    type Output = ();
    type Input = P::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        let save = src.clone();
        match self.p.parse(src) {
            Ok((_, _)) => Err((Error::Expect, save)),
            Err((_, _)) => Ok(((), save)),
        }
    }
}

/// Make a parser that tests the argument parser doesn't match following tokens.
///
/// ```
/// use rparse::prim::{Parser, exact};
/// use rparse::combinator::not_followed_by;
///
/// let t_ex = exact('t');
/// let src = "te".chars().peekable();
/// let mut not_p = not_followed_by(t_ex);
/// let res = not_p.parse(src);
/// assert!(res.is_err());
/// if let Err((_, ctx)) = res {
///     assert_eq!(vec!['t', 'e'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn not_followed_by<I: Clone, P: Parser<Input=I>>(p: P) -> NotFollowedBy<I, P> {
    NotFollowedBy { p: p }
}

#[test]
fn not_followed_by_test() {
    let t_ex = exact('t');
    let src = "te".chars().peekable();
    let mut not_p = not_followed_by(t_ex);
    let res = not_p.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['t', 'e'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that matches sequence of parser1 and parser2.
pub struct Seq<I: Clone, P1: Parser<Input=I>, P2: Parser<Input=I>> {
    p1: P1,
    p2: P2,
}

impl <In: Clone, P1, P2> Parser for Seq<In, P1, P2>
where P1: Parser<Input=In>, P2: Parser<Input=P1::Input> {
    type Output = (P1::Output, P2::Output);
    type Input = P1::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        let save = src.clone();
        let (r1, ctx) = try!(self.p1.parse(src));
        let (r2, ctx) = match self.p2.parse(ctx) {
            Ok((r2, ctx)) => (r2, ctx),
            Err((e, _)) => return Err((e, save)),
        };
        Ok(((r1, r2), ctx))
    }
}

/// Make a parser that matches a sequence of parser1 and parser2.
///
/// ```
/// use rparse::prim::{Parser, exact};
/// use rparse::combinator::seq;

/// let a_ex = exact('a');
/// let b_ex = exact('b');
/// let mut seq_ab = seq(a_ex, b_ex);
/// let src = "abc".chars().peekable();
/// let res = seq_ab.parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!(('a', 'b'), r);
///     assert_eq!(vec!['c'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn seq<I, P1, P2>(p1: P1, p2: P2) -> Seq<I, P1, P2>
where I: Clone, P1: Parser<Input=I>, P2: Parser<Input=I> {
    Seq { p1: p1, p2: p2 }
}

#[test]
fn seq_test() {
    let a_ex = exact('a');
    let b_ex = exact('b');
    let mut seq_ab = seq(a_ex, b_ex);
    let src = "abc".chars().peekable();
    let res = seq_ab.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!(('a', 'b'), r);
        assert_eq!(vec!['c'], ctx.collect::<Vec<_>>());
    }

    let src = "acd".chars().peekable();
    let res = seq_ab.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['a', 'c', 'd'], ctx.collect::<Vec<_>>());
    }
}
