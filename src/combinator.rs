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

    /// Test the following tokens can match the argument parser
    ///
    /// ```
    /// use rparse::prim::{Parser, exact};
    /// use rparse::combinator::{AdvancedParser};
    ///
    /// let a_ex = exact('a');
    /// let b_ex = exact('b');
    /// let mut parser = a_ex.followed_by(b_ex);
    /// let res = parser.parse("abc".chars().peekable());
    ///
    /// assert!(res.is_ok());
    /// if let Ok((r, ctx)) = res {
    ///     assert_eq!('a', r);
    ///     assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
    /// }
    /// ```
    fn followed_by<P: Parser<Input=Self::Input> + Clone>(self, p: P)
        -> FollowedBy<Self, P>;

    /// Test the following tokens cannot match the argument parser
    ///
    /// ```
    /// use rparse::prim::{Parser, exact};
    /// use rparse::combinator::{AdvancedParser};
    ///
    /// let a_ex = exact('a');
    /// let b_ex = exact('b');
    /// let mut parser = a_ex.not_followed_by(b_ex);
    /// let res = parser.parse("abc".chars().peekable());
    ///
    /// assert!(res.is_err());
    /// if let Err((_, ctx)) = res {
    ///     assert_eq!(vec!['a', 'b', 'c'], ctx.collect::<Vec<_>>());
    /// }
    /// ```
    fn not_followed_by<P: Parser<Input=Self::Input> + Clone>(self, p: P)
        -> NotFollowedBy<Self, P>;

    /// Test parser1, and then test parser2.
    /// Return the tuple of those return values.
    ///
    /// ```
    /// use rparse::prim::{Parser, exact};
    /// use rparse::combinator::AdvancedParser;
    ///
    /// let a_ex = exact('a');
    /// let b_ex = exact('b');
    /// let mut parser = a_ex.and(b_ex);
    /// let res = parser.parse("abc".chars().peekable());
    ///
    /// assert!(res.is_ok());
    /// if let Ok((r, ctx)) = res {
    ///     assert_eq!(('a', 'b'), r);
    ///     assert_eq!(vec!['c'], ctx.collect::<Vec<_>>());
    /// }
    /// ```
    fn and<P: Parser<Input=Self::Input> + Clone>(self, p: P)
        -> Seq<Self::Input, Self, P>;

    /// Test parser1, and then test parser2 and skip it.
    ///
    /// ```
    /// use rparse::prim::{Parser, exact};
    /// use rparse::combinator::AdvancedParser;
    ///
    /// let a_ex = exact('a');
    /// let comma = exact(',');
    /// let b_ex = exact('b');
    /// let mut parser = a_ex.skip(comma).and(b_ex);
    /// let res = parser.parse("a,b".chars().peekable());
    ///
    /// assert!(res.is_ok());
    /// if let Ok((r, ctx)) = res {
    ///     assert_eq!(('a', 'b'), r);
    /// }
    /// ```
    fn skip<P: Parser<Input=Self::Input> + Clone>(self, p: P)
        -> Skip<Self, P>;
}

impl <I: Clone, P: Clone + Parser<Input=I>> AdvancedParser for P {
    fn map<B, F>(self, f: F) -> Map<Self, F>
    where F: FnMut(Self::Output) -> B {
        Map { p: self, f: f }
    }

    fn followed_by<T: Parser<Input=Self::Input> + Clone>(self, p: T)
        -> FollowedBy<Self, T> {
        FollowedBy { p: self, follow: p }
    }

    fn not_followed_by<T: Parser<Input=Self::Input> + Clone>(self, p: T)
        -> NotFollowedBy<Self, T> {
        NotFollowedBy { p: self, not_follow: p }
    }

    fn and<T: Parser<Input=Self::Input> + Clone>(self, p: T)
        -> Seq<Self::Input, Self, T> {
        Seq { p1: self, p2: p }
    }

    fn skip<T: Parser<Input=Self::Input> + Clone>(self, p: T)
        -> Skip<Self, T> {
        Skip { p: self, skip: p }
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
pub struct FollowedBy<P1: Parser, P2: Parser<Input=P1::Input>> {
    p: P1,
    follow: P2
}
impl <P1: Parser, P2: Parser<Input=P1::Input>> Parser for FollowedBy<P1, P2> {
    type Output = P1::Output;
    type Input = P1::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        let save = src.clone();
        let res = match self.p.parse(src) {
            Ok(r) => r,
            Err((e, _)) => return Err((e, save))
        };
        let save2 = res.1.clone();
        match self.follow.parse(res.1) {
            Ok((_, _)) => Ok((res.0, save2)),
            Err((e, _)) => Err((e, save)),
        }
    }
}

#[test]
fn followed_by_test() {
    let t_ex = exact('t');
    let e_ex = exact('e');
    let src = "test".chars().peekable();
    let mut and_p = t_ex.followed_by(e_ex);
    let res = and_p.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!('t', r);
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that doesn't consume any token of the source.
/// It only tests the argument parser won't match following tokens.
pub struct NotFollowedBy<P1: Parser, P2: Parser<Input=P1::Input>> {
    p: P1,
    not_follow: P2,
}
impl <P1: Parser, P2: Parser<Input=P1::Input>> Parser for NotFollowedBy<P1, P2> {
    type Output = P1::Output;
    type Input = P1::Input;

    fn parse<I>(&mut self, src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        let save = src.clone();
        let res = match self.p.parse(src) {
            Ok(ret) => ret,
            Err((e, _)) => return Err((e, save)),
        };
        let save2 = res.1.clone();
        match self.not_follow.parse(res.1) {
            Ok((_, _)) => Err((Error::Expect, save)),
            Err((_, _)) => Ok((res.0, save2)),
        }
    }
}


#[test]
fn not_followed_by_test() {
    let t_ex = exact('t');
    let e_ex = exact('s');
    let src = "te".chars().peekable();
    let mut not_p = t_ex.not_followed_by(e_ex);
    let res = not_p.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!('t', r);
        assert_eq!(vec!['e'], ctx.collect::<Vec<_>>());
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


#[test]
fn seq_test() {
    let a_ex = exact('a');
    let b_ex = exact('b');
    let mut seq_ab = a_ex.and(b_ex);
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

#[derive(Debug, Clone)]
/// A parser that test the first pattern and skip the second pattern
pub struct Skip<P1: Parser, P2: Parser<Input=P1::Input>> {
    p: P1,
    skip: P2,
}

impl <P1: Parser, P2: Parser<Input=P1::Input>> Parser for Skip<P1, P2> {
    type Output = P1::Output;
    type Input = P1::Input;

    fn parse<I>(&mut self, src: Peekable<I>) -> ParseResult<Self::Output, Peekable<I>>
    where I: Clone + Iterator<Item=Self::Input> {
        let save = src.clone();
        let res = match self.p.parse(src) {
            Ok(res) => res,
            Err(e) => return Err(e),
        };
        match self.skip.parse(res.1) {
            Ok((_, ctx)) => Ok((res.0, ctx)),
            Err((e, _)) => Err((e, save)),
        }
    }
}

