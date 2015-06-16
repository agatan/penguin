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

struct AndParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for AndParser<In, P> {
    type Output = ();
    type Input = P::Input;

    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {
        let save = src.clone();
        match self.p.parse(src) {
            Ok((_, _)) => Ok(((), save)),
            Err((e, _)) => Err((e, save))
        }
    }
}
fn and<I: Clone, P: Parser<Input=I>>(p: P) -> AndParser<I, P> {
    AndParser { p : p }
}

#[test]
fn and_test() {
    let t_ex = exact('t');
    let src = "test".chars().peekable();
    let and_p = and(t_ex);
    let res = and_p.parse(src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

struct NotParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for NotParser<In, P> {
    type Output = ();
    type Input = P::Input;

    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        let save = src.clone();
        match self.p.parse(src) {
            Ok((_, _)) => Err((Error::Expect, save)),
            Err((_, _)) => Ok(((), save)),
        }
    }
}

fn not<I: Clone, P: Parser<Input=I>>(p: P) -> NotParser<I, P> {
    NotParser { p: p }
}

#[test]
fn not_test() {
    let t_ex = exact('t');
    let src = "te".chars().peekable();
    let not_p = not(t_ex);
    let res = not_p.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['t', 'e'], ctx.collect::<Vec<_>>());
    }
}

struct OptionParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for OptionParser<In, P> {
    type Output = Option<P::Output>;
    type Input = P::Input;

    fn parse<I>(&self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Clone + Iterator<Item=Self::Input> {

        match self.p.parse(src) {
            Ok((r, ctx)) => Ok((Some(r), ctx)),
            Err((_, ctx)) => Ok((None, ctx)),
        }
    }
}

fn option<I: Clone, P: Parser<Input=I>>(p: P) -> OptionParser<I, P> {
    OptionParser { p : p }
}

#[test]
fn option_test() {
    let str_test = string("tes");
    let src = "test".chars().peekable();
    let opt = option(str_test);
    let res = opt.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!((), r.unwrap());
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }

    let str_test = string("example");
    let src = "test".chars().peekable();
    let opt = option(str_test);
    let res = opt.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert!(r.is_none());
        assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

struct ManyParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for ManyParser<In, P> {
    type Output = Vec<P::Output>;
    type Input = P::Input;

    fn parse<I>(&self, mut src: Peekable<I>)
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
                    return Ok((ret, ctx));
                }
            }
        }
    }
}

fn many<I: Clone, P: Parser<Input=I>>(p: P) -> ManyParser<I, P> {
    ManyParser { p: p }
}

#[test]
fn many_test() {
    let a_ex = exact('a');
    let src = "aaaabb".chars().peekable();
    let many_p = many(a_ex);
    let res: Result<(Vec<_>, _), _> = many_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert_eq!(vec![(), (), (), ()], v);
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }

    let a_ex = exact('a');
    let src = "bb".chars().peekable();
    let many_p = many(a_ex);
    let res: Result<(Vec<_>, _), _> = many_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert!(v.is_empty());
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }
}

#[cfg(not(test))]
fn main() {}
