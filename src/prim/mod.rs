//! primitive parsers are defined here.

pub mod helper;
pub use self::helper::{option, many, many1, select, success};

use std::iter::{Iterator, Peekable};
use std::marker::PhantomData;

/// Parse Error. This is still a placeholder.
/// This will be more useful error message in the future.
pub enum Error {
    /// represent the expected token there.
    Expect
}

/// This is a result type of parse.
/// `Ok` value and `Err` value have a context of parse (rest of stream that is parsed)
/// `Res` is a return type of parse if succeeded.
/// `P` is a parser context type
pub type ParseResult<Res, P> = Result<(Res, P), (Error, P)>;

/// This is a main trait of this parser library.
/// If you want to parse string, `Input` may be `char`.
pub trait Parser {
    /// `Output` is a type of parse when the parse succeeded.
    type Output;
    /// `Input` is a type of stream's element that is parsed.
    type Input: Clone;
    /// returns parse result and context of parse.
    /// If you want to parse string, `src` may be `Peekable<char>`
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> + Clone;
}

#[derive(Debug, Clone)]
/// A most primitive parser. This matches all tokens.
pub struct AnyParser<I> {
    _mark: PhantomData<I>
}
impl <In: Clone> Parser for AnyParser<In> {
    type Output = ();
    type Input = In;
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> {
        if src.peek().is_none() {
            Err((Error::Expect, src))
        } else {
            let _ = src.next();
            Ok(((), src))
        }
    }
}

/// Make a parser that matches all tokens.
///
/// ```
/// use rparse::prim::{Parser, any};
///
/// let src = "test".chars().peekable();
/// let mut any_parser = any();
/// let res = any_parser.parse(src);
/// assert!(res.is_ok());
/// if let Ok((res, ctx)) = res {
///     assert!(res == ());
///     assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn any<I>() -> AnyParser<I> {
    AnyParser { _mark: PhantomData }
}

#[test]
fn any_test() {
    let src = "test".chars().peekable();
    let mut any_parser = any();
    if let Ok((res, ctx)) = any_parser.parse(src) {
        assert!(res == ());
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("any returns Err");
    }

    let src = vec![1, 2, 3];
    let src2 = src.iter().peekable();
    let mut any_parser = any();
    if let Ok((res, ctx)) = any_parser.parse(src2) {
        assert!(res == ());
        assert_eq!(vec![&2, &3], ctx.collect::<Vec<_>>());
    } else {
        panic!("any returns Err");
    }
}

#[derive(Debug, Clone)]
/// A parser that matches a token that is equal to the needle.
pub struct ExactParser<I> {
    needle: I,
}
impl <In: PartialEq + Clone> Parser for ExactParser<In> {
    type Output = In;
    type Input = In;
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> {
        if src.peek() == Some(&self.needle) {
            let _ = src.next();
            Ok((self.needle.clone(), src))
        } else {
            Err((Error::Expect, src))
        }
    }
}

/// Make a parser. The parser matches a token that is equal to the argument.
///
/// ```
/// use rparse::prim::{Parser, exact};
///
/// let src = "test".chars().peekable();
/// let mut parser = exact('t');
/// let res = parser.parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!('t', r);
///     assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn exact<T>(t: T) -> ExactParser<T> where T: PartialEq {
    ExactParser { needle: t }
}

#[test]
fn exact_test() {
    let src = "test".chars().peekable();
    let mut parser = exact('t');
    if let Ok((r, ctx)) = parser.parse(src) {
        assert_eq!('t', r);
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("exact return Err");
    }
}

#[derive(Debug, Clone)]
/// A parser that matches when the source is empty.
pub struct EndParser<I> {
    _mark: PhantomData<I>,
}
impl <In: Clone> Parser for EndParser<In> {
    type Output = ();
    type Input = In;
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> {
        if src.peek().is_none() {
            Ok(((), src))
        } else {
            Err((Error::Expect, src))
        }
    }
}

/// Make a parser that matches when the source is empty.
///
/// ```
/// use rparse::prim::{Parser, end};
///
/// let mut end_parser = end();
/// let src = "".chars().peekable();
/// assert!(end_parser.parse(src).is_ok());
/// let src = "a".chars().peekable();
/// assert!(!end_parser.parse(src).is_ok());
/// ```
pub fn end<I>() -> EndParser<I> {
    EndParser { _mark: PhantomData }
}

#[test]
fn end_test() {
    let mut end_parser = end();
    let src = "".chars().peekable();
    assert!(end_parser.parse(src).is_ok());
    let src = "a".chars().peekable();
    assert!(!end_parser.parse(src).is_ok());
}

#[derive(Debug, Clone)]
/// A parser for string. This matches string, and consume the charactors of the source.
pub struct StringParser<'a> {
    ss: &'a str
}
impl <'a> Parser for StringParser<'a> {
    type Output = String;
    type Input = char;
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        let save = src.clone();
        for c in self.ss.chars() {
            if src.peek().is_none() || src.peek() != Some(&c) {
                return Err((Error::Expect, save));
            }
            let _ = src.next();
        }
        Ok((self.ss.to_string(), src))
    }
}


/// Make a parser that matches the argument string.
///
/// ```
/// use rparse::prim::{Parser, string};
///
/// let src = "test".chars().peekable();
/// let mut parser = string("tes");
/// let res = parser.parse(src);
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!("tes".to_string(), r);
///     assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn string<'a>(s: &'a str) -> StringParser<'a> {
    StringParser { ss: s }
}

#[test]
fn string_test() {
    let src = "test".chars().peekable();
    let mut parser = string("tes");
    let res = parser.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!("tes".to_string(), r);
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
/// A parser that matches any token in the set.
pub struct SetParser<'a, T: 'a + PartialEq> {
    ss: &'a [T],
}
impl <'a, T: PartialEq + Clone> Parser for SetParser<'a, T> {
    type Output = T;
    type Input = T;
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        if src.peek().is_none() {
            return Err((Error::Expect, src));
        }
        for c in self.ss {
            if src.peek() == Some(c) {
                let _ = src.next();
                return Ok((c.clone(), src));
            }
        }
        Err((Error::Expect, src))
    }
}

/// Make a parser that matches any token in the argument set.
///
/// ```
/// use rparse::prim::{Parser, set};
///
/// let ss = vec!['s', 't', 'u'];
/// let mut p = set(&ss);
/// let src = "test".chars().peekable();
/// let res = p.parse(src);
/// assert!(res.is_ok());
/// if let Ok(('t', ctx)) = res {
///     assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
/// }
/// ```
pub fn set<'a, T: PartialEq>(ss: &'a [T]) -> SetParser<'a, T> {
    SetParser { ss: ss }
}

#[test]
fn set_test() {
    let ss = vec!['s', 't', 'u'];
    let mut p = set(&ss);
    let src = "test".chars().peekable();
    let res = p.parse(src);
    assert!(res.is_ok());
    if let Ok(('t', ctx)) = res {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}


#[derive(Debug, Clone)]
/// A parser that tests whether the following token satisfy the condition.
pub struct Satisfy<I, F: FnMut(&I) -> bool> {
    f: F,
    _mark: PhantomData<I>
}

impl <In: Clone, F: FnMut(&In) -> bool> Parser for Satisfy<In, F> {
    type Output = In;
    type Input = In;

    fn parse<I>(&mut self, mut src: Peekable<I>) -> ParseResult<Self::Output, Peekable<I>>
    where I: Clone + Iterator<Item=Self::Input> {
        let ret = src.peek().map(|t| (self.f)(t));
        if let Some(true) = ret {
            let t = src.peek().unwrap().clone();
            let _ = src.next();
            Ok((t, src))
        } else {
            Err((Error::Expect, src))
        }
    }
}

/// Make a parser that matches the token satisfied the condition.
///
/// ```
/// use rparse::prim::{Parser, satisfy};
///
/// let src = "test".chars().peekable();
/// let mut parser = satisfy(|t| 'o' < *t && *t < 'z');
/// let res = parser.parse(src);
///
/// assert!(res.is_ok());
/// if let Ok((r, ctx)) = res {
///     assert_eq!('t', r);
///     assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
/// }
pub fn satisfy<I: Clone, F: FnMut(&I) -> bool>(pred: F) -> Satisfy<I, F> {
    Satisfy { f: pred, _mark: PhantomData }
}
