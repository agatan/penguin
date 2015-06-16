use std::iter::{Iterator, Peekable};
use std::marker::PhantomData;

pub enum Error {
    Expect
}

pub type ParseResult<Res, P> = Result<(Res, P), (Error, P)>;

pub trait Parser {
    type Output;
    type Input;
    fn parse<I>(&mut self, mut src: Peekable<I>)
        -> ParseResult<Self::Output, Peekable<I>>
        where I: Iterator<Item=Self::Input> + Clone;
}

#[derive(Debug, Clone)]
pub struct AnyParser<I> {
    _mark: PhantomData<I>
}
impl <In> Parser for AnyParser<In> {
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
pub struct ExactParser<I> {
    needle: I,
}
impl <In: PartialEq> Parser for ExactParser<In> {
    type Output = ();
    type Input = In;
    fn parse<I>(&mut self, mut src: Peekable<I>)
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

pub fn exact<T>(t: T) -> ExactParser<T> where T: PartialEq {
    ExactParser { needle: t }
}

#[test]
fn exact_test() {
    let src = "test".chars().peekable();
    let mut parser = exact('t');
    if let Ok(((), ctx)) = parser.parse(src) {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("exact return Err");
    }
}

#[derive(Debug, Clone)]
pub struct EndParser<I> {
    _mark: PhantomData<I>,
}
impl <In> Parser for EndParser<In> {
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
pub struct StringParser<'a> {
    ss: &'a str
}
impl <'a> Parser for StringParser<'a> {
    type Output = ();
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
        Ok(((), src))
    }
}


pub fn string<'a>(s: &'a str) -> StringParser<'a> {
    StringParser { ss: s }
}

#[test]
fn string_test() {
    let src = "test".chars().peekable();
    let mut parser = string("tes");
    let res = parser.parse(src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
pub struct SetParser<'a, T: 'a + PartialEq> {
    ss: &'a [T],
}
impl <'a, T: PartialEq> Parser for SetParser<'a, T> {
    type Output = ();
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
                return Ok(((), src));
            }
        }
        Err((Error::Expect, src))
    }
}

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
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
pub struct AndParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for AndParser<In, P> {
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
pub fn and<I: Clone, P: Parser<Input=I> + Clone>(p: &P) -> AndParser<I, P> {
    AndParser { p : p.clone() }
}

#[test]
fn and_test() {
    let t_ex = exact('t');
    let src = "test".chars().peekable();
    let mut and_p = and(&t_ex);
    let res = and_p.parse(src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
pub struct NotParser<I: Clone, P: Parser<Input=I>> {
    p: P,
}
impl <In: Clone, P: Parser<Input=In>> Parser for NotParser<In, P> {
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

pub fn not<I: Clone, P: Parser<Input=I> + Clone>(p: &P) -> NotParser<I, P> {
    NotParser { p: p.clone() }
}

#[test]
fn not_test() {
    let t_ex = exact('t');
    let src = "te".chars().peekable();
    let mut not_p = not(&t_ex);
    let res = not_p.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['t', 'e'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
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

pub fn option<I: Clone, P: Parser<Input=I> + Clone>(p: &P) -> OptionParser<I, P> {
    OptionParser { p : p.clone() }
}

#[test]
fn option_test() {
    let str_test = string("tes");
    let src = "test".chars().peekable();
    let mut opt = option(&str_test);
    let res = opt.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!((), r.unwrap());
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }

    let str_test = string("example");
    let src = "test".chars().peekable();
    let mut opt = option(&str_test);
    let res = opt.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert!(r.is_none());
        assert_eq!(vec!['t', 'e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
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

pub fn many<I: Clone, P: Parser<Input=I> + Clone>(p: &P) -> ManyParser<I, P> {
    ManyParser { p: p.clone() }
}

#[test]
fn many_test() {
    let a_ex = exact('a');
    let src = "aaaabb".chars().peekable();
    let mut many_p = many(&a_ex);
    let res: Result<(Vec<_>, _), _> = many_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert_eq!(vec![(), (), (), ()], v);
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }

    let a_ex = exact('a');
    let src = "bb".chars().peekable();
    let mut many_p = many(&a_ex);
    let res: Result<(Vec<_>, _), _> = many_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert!(v.is_empty());
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
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

pub fn many1<I: Clone, P: Clone + Parser<Input=I>>(p : &P) -> Many1Parser<I, P> {
    Many1Parser { p : p.clone() }
}

#[test]
fn many1_parser() {
    let a_ex = exact('a');
    let src = "aaaabb".chars().peekable();
    let mut many1_p = many1(&a_ex);
    let res: Result<(Vec<_>, _), _> = many1_p.parse(src);
    assert!(res.is_ok());
    if let Ok((v, ctx)) = res {
        assert_eq!(vec![(), (), (), ()], v);
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }

    let a_ex = exact('a');
    let src = "bb".chars().peekable();
    let mut many1_p = many1(&a_ex);
    let res: Result<(Vec<_>, _), _> = many1_p.parse(src);
    assert!(res.is_err());
    if let Err((_, ctx)) = res {
        assert_eq!(vec!['b', 'b'], ctx.collect::<Vec<_>>());
    }
}

#[derive(Debug, Clone)]
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

pub fn seq<I, P1, P2>(p1: &P1, p2: &P2) -> SeqParser<I, P1, P2>
where I: Clone, P1: Clone + Parser<Input=I>, P2: Clone + Parser<Input=I> {
    SeqParser { p1: p1.clone(), p2: p2.clone() }
}

#[test]
fn seq_test() {
    let a_ex = exact('a');
    let b_ex = exact('b');
    let mut seq_ab = seq(&a_ex, &b_ex);
    let src = "abc".chars().peekable();
    let res = seq_ab.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!(((), ()), r);
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

pub fn select<I, P1, P2>(p1: &P1, p2: &P2) -> SelectParser<I, P1, P2>
where I: Clone, P1: Clone + Parser<Input=I>,
                P2: Clone + Parser<Input=I, Output=P1::Output> {
    SelectParser { p1: p1.clone(), p2: p2.clone() }
}

#[test]
fn select_test() {
    let a_ex = exact('a');
    let b_ex = exact('b');
    let mut sel_ab = select(&a_ex, &b_ex);
    let src = "abc".chars().peekable();
    let res = sel_ab.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!((), r);
        assert_eq!(vec!['b', 'c'], ctx.collect::<Vec<_>>());
    }
    let src = "bac".chars().peekable();
    let res = sel_ab.parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!((), r);
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

pub fn success<I, P>(p: &P) -> SuccessParser<I, P>
where I: Clone, P: Clone + Parser<Input=I> {
    SuccessParser { p : p.clone() }
}

#[test]
fn success_test() {
    let seq_ab = seq(&exact('a'), &exact('b'));
    let src = "abc".chars().peekable();
    let res = success(&seq_ab).parse(src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!((), r);
        assert_eq!(vec!['c'], ctx.collect::<Vec<_>>());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::{Iterator, Peekable};

    #[test]
    fn digits_test() {
        let non_z = ['1', '2', '3', '4', '5', '6', '7', '8', '9'];
        let non_zero = set(&non_z);
        let digit = select(&exact('0'), &non_zero);
        let dig_head = seq(&seq(&non_zero, &option(&digit)), &option(&digit));
        let dig_tail = seq(&seq(&seq(&exact(','), &digit), &digit), &digit);
        let zero = success(&seq(&exact('0'), &end()));
        let mut digits = select(&zero, &success(&seq(&seq(&dig_head, &many(&dig_tail)), &end())));

        for s in ["0", "1", "1,234"].iter() {
            let src = s.chars().peekable();
            let ret = digits.parse(src);
            assert!(ret.is_ok());
            if let Ok(((), mut ctx)) = ret {
                assert!(ctx.peek().is_none());
            }
        }
    }
}
