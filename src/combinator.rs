//! Parser combinators are defined here.
//! Using them, you can make a new parser of some primitive parsers.
//! Parsers made of some primitive parsers are also parser,
//! so you can combine them with any other parsers.

use prim::*;

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
/// A optional parser.
pub struct OptionParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for OptionParser<In, P> {
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
pub fn option<I: Clone, P: Parser<Input=I>>(p: P) -> OptionParser<I, P> {
    OptionParser { p : p }
}

#[test]
fn option_test() {
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
pub struct ManyParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for ManyParser<In, P> {
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
pub fn many<I: Clone, P: Parser<Input=I>>(p: P) -> ManyParser<I, P> {
    ManyParser { p: p }
}

#[test]
fn many_test() {
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
pub struct Many1Parser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for Many1Parser<In, P> {
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
pub fn many1<I: Clone, P: Parser<Input=I>>(p : P) -> Many1Parser<I, P> {
    Many1Parser { p : p }
}

#[test]
fn many1_parser() {
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
/// A parser that matches sequence of parser1 and parser2.
pub struct SeqParser<I: Clone, P1: Parser<Input=I>, P2: Parser<Input=I>> {
    p1: P1,
    p2: P2,
}

impl <In: Clone, P1, P2> Parser for SeqParser<In, P1, P2>
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
pub fn seq<I, P1, P2>(p1: P1, p2: P2) -> SeqParser<I, P1, P2>
where I: Clone, P1: Parser<Input=I>, P2: Parser<Input=I> {
    SeqParser { p1: p1, p2: p2 }
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

#[derive(Debug, Clone)]
/// A parser that matches either parser1 or parser2.
pub struct SelectParser<I, P1, P2>
where I: Clone, P1: Parser<Input=I>, P2: Parser<Input=I, Output=P1::Output> {
    p1: P1,
    p2: P2,
}

impl <In, P1, P2> Parser for SelectParser<In, P1, P2>
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
pub fn select<I, P1, P2>(p1: P1, p2: P2) -> SelectParser<I, P1, P2>
where I: Clone, P1: Parser<Input=I>,
                P2: Parser<Input=I, Output=P1::Output> {
    SelectParser { p1: p1, p2: p2 }
}

#[test]
fn select_test() {
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
pub struct SuccessParser<I, P>
where I: Clone, P: Parser<Input=I> {
    p: P,
}
impl <I: Clone, P: Parser<Input=I>> Parser for SuccessParser<I, P> {
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
pub fn success<I, P>(p: P) -> SuccessParser<I, P>
where I: Clone, P: Parser<Input=I> {
    SuccessParser { p : p }
}

#[test]
fn success_test() {
    let seq_ab = seq(exact('a'), exact('b'));
    let src = "abc".chars().peekable();
    let res = success(seq_ab).parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!((), r);
        assert_eq!(vec!['c'], ctx.collect::<Vec<_>>());
    }
}
