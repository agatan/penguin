use std::iter::{Iterator, Peekable};
use std::marker::PhantomData;

enum Error {
    Expect
}

type ParseResult<Res, P> = Result<(Res, P), (Error, P)>;

trait Parser {
    type Output;
    type Input;
    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> + Clone;
}

struct AnyParser<I> {
    _mark: PhantomData<I>
}
impl <In> Parser for AnyParser<In> {
    type Output = ();
    type Input = In;
    fn parse<I>(&self, mut src: Peekable<I>)
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

fn any<I>() -> AnyParser<I> {
    AnyParser { _mark: PhantomData }
}

#[test]
fn any_test() {
    let src = "test".chars().peekable();
    let any_parser = any();
    if let Ok((res, ctx)) = any_parser.parse(src) {
        assert!(res == ());
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("any returns Err");
    }

    let src = vec![1, 2, 3];
    let src2 = src.iter().peekable();
    let any_parser = any();
    if let Ok((res, ctx)) = any_parser.parse(src2) {
        assert!(res == ());
        assert_eq!(vec![&2, &3], ctx.collect::<Vec<_>>());
    } else {
        panic!("any returns Err");
    }
}

struct ExactParser<I> {
    needle: I,
}
impl <In: PartialEq> Parser for ExactParser<In> {
    type Output = ();
    type Input = In;
    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> {
        if src.peek() == Some(&self.needle) {
            let _ = src.next();
            Ok(((), src))
        } else {
            Err((Error::Expect, src))
        }
    }
}

fn exact<T>(t: T) -> ExactParser<T> where T: PartialEq {
    ExactParser { needle: t }
}

#[test]
fn exact_test() {
    let src = "test".chars().peekable();
    let parser = exact('t');
    if let Ok(((), ctx)) = parser.parse(src) {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("exact return Err");
    }
}

struct EndParser<I> {
    _mark: PhantomData<I>,
}
impl <In> Parser for EndParser<In> {
    type Output = ();
    type Input = In;
    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> {
        if src.peek().is_none() {
            Ok(((), src))
        } else {
            Err((Error::Expect, src))
        }
    }
}


fn end<I>() -> EndParser<I> {
    EndParser { _mark: PhantomData }
}

#[test]
fn end_test() {
    let end_parser = end();
    let src = "".chars().peekable();
    assert!(end_parser.parse(src).is_ok());
    let src = "a".chars().peekable();
    assert!(!end_parser.parse(src).is_ok());
}

struct StringParser<'a> {
    ss: &'a str
}
impl <'a> Parser for StringParser<'a> {
    type Output = ();
    type Input = char;
    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        let save = src.clone();
        for c in self.ss.chars() {
            if src.peek().is_none() || src.peek() != Some(&c) {
                return Err((Error::Expect, save));
            }
            let _ = src.next();
        }
        Ok(((), src))
    }
}


fn string<'a>(s: &'a str) -> StringParser<'a> {
    StringParser { ss: s }
}

#[test]
fn string_test() {
    let src = "test".chars().peekable();
    let parser = string("tes");
    let res = parser.parse(src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }
}

struct SetParser<'a, T: 'a + PartialEq> {
    ss: &'a [T],
}
impl <'a, T: PartialEq> Parser for SetParser<'a, T> {
    type Output = ();
    type Input = T;
    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        if src.peek().is_none() {
            return Err((Error::Expect, src));
        }
        for c in self.ss {
            if src.peek() == Some(c) {
                let _ = src.next();
                return Ok(((), src));
            }
        }
        Err((Error::Expect, src))
    }
}

fn set<'a, T: PartialEq>(ss: &'a [T]) -> SetParser<'a, T> {
    SetParser { ss: ss }
}

#[test]
fn set_test() {
    let ss = vec!['s', 't', 'u'];
    let p = set(&ss);
    let src = "test".chars().peekable();
    let res = p.parse(src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}



#[cfg(not(test))]
fn main() {}
