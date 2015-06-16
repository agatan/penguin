use std::iter::{Iterator, Peekable};

enum Error {
    Expect
}


type ParseResult<Res, P> = Result<(Res, P), (Error, P)>;

fn any<T, I>(mut src: Peekable<I>) -> ParseResult<bool, Peekable<I>>
    where I: Iterator<Item=T> {
    if src.peek().is_none() {
        Err((Error::Expect, src))
    } else {
        let _ = src.next();
        Ok((true, src))
    }
}

#[test]
fn any_test() {
    let src = "test".chars().peekable();
    if let Ok((res, ctx)) = any(src) {
        assert!(res);
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("any returns Err");
    }

    let src = vec![1, 2, 3];
    let src2 = src.iter().peekable();
    if let Ok((res, ctx)) = any(src2) {
        assert!(res);
        assert_eq!(vec![&2, &3], ctx.collect::<Vec<_>>());
    } else {
        panic!("any returns Err");
    }
}

fn exact<T, I>(t: &T, mut src: Peekable<I>) -> ParseResult<(), Peekable<I>>
    where T: PartialEq + Clone, I: Iterator<Item=T> {
    if src.peek() == Some(t) {
        let _ = src.next();
        Ok(((), src))
    } else {
        Err((Error::Expect, src))
    }
}

#[test]
fn exact_test() {
    let src = "test".chars().peekable();
    if let Ok(((), ctx)) = exact(&'t', src) {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    } else {
        panic!("exact return Err");
    }
}

fn end<T, I>(mut src: Peekable<I>) -> ParseResult<(), Peekable<I>>
    where I: Iterator<Item=T> {
    if src.peek().is_none() {
        Ok(((), src))
    } else {
        Err((Error::Expect, src))
    }
    }

#[test]
fn end_test() {
    let src = "".chars().peekable();
    assert!(end(src).is_ok());
    let src = "a".chars().peekable();
    assert!(!end(src).is_ok());
}

fn string<I>(s: &str, mut src: Peekable<I>) -> ParseResult<(), Peekable<I>>
    where I: Clone + Iterator<Item=char> {
    let save = src.clone();
    for c in s.chars() {
        if src.peek().is_none() || src.peek() != Some(&c) {
            return Err((Error::Expect, save));
        }
        let _ = src.next();
    }
    Ok(((), src))
}

#[test]
fn string_test() {
    let src = "test".chars().peekable();
    let res = string("tes", src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['t'], ctx.collect::<Vec<_>>());
    }
}

fn set<T, I>(ss: &[T], mut src: Peekable<I>) -> ParseResult<(), Peekable<I>>
    where T: PartialEq, I: Iterator<Item=T> {
    if src.peek().is_none() {
        return Err((Error::Expect, src));
    }
    for c in ss {
        if src.peek() == Some(c) {
            let _ = src.next();
            return Ok(((), src));
        }
    }
    Err((Error::Expect, src))
}

#[test]
fn set_test() {
    let ss = vec!['s', 't', 'u'];
    let src = "test".chars().peekable();
    let res = set(&ss, src);
    assert!(res.is_ok());
    if let Ok(((), ctx)) = res {
        assert_eq!(vec!['e', 's', 't'], ctx.collect::<Vec<_>>());
    }
}

fn range<T, I>(s1: &T, s2: &T, mut src: Peekable<I>)
    -> ParseResult<T, Peekable<I>>
    where T: PartialOrd + Clone, I: Iterator<Item=T> {
    if src.peek().is_none() {
        return Err((Error::Expect, src));
    }
    let c = src.peek().unwrap().clone();
    if s1 <= &c && &c < s2 {
        let _ = src.next();
        return Ok((c, src));
    }
    Err((Error::Expect, src))
}

#[test]
fn range_test() {
    let s1 = 'a';
    let s2 = 'e';
    let src = "com".chars().peekable();
    let res = range(&s1, &s2, src);
    assert!(res.is_ok());
    if let Ok((r, ctx)) = res {
        assert_eq!('c', r);
        assert_eq!(vec!['o', 'm'], ctx.collect::<Vec<_>>());
    }
}
