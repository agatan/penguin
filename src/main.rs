use std::str::FromStr;

trait Range<T> {
    fn empty(&self) -> bool;
    fn front(&self) -> &T;
    fn pop_front(&mut self);
    fn save(&self) -> Self;
}

impl <'a, T> Range<T> for &'a [T] {
    fn empty(&self) -> bool {
        self.len() == 0
    }

    fn front(&self) -> &T {
        &self[0]
    }

    fn pop_front(&mut self) {
        *self = &self[1..];
    }

    fn save(&self) -> Self {
        self.clone()
    }
}

fn from_str(src: &str) -> Vec<char> {
    src.chars().collect::<Vec<_>>()
}

#[derive(PartialEq, Debug)]
struct ParseContext<R> {
    ctx: R
}

impl <R> ParseContext<R> {
    fn new(r: R) -> Self {
        ParseContext { ctx : r }
    }
}

type ParseResult<Res, R> = Result<Res, ParseContext<R>>;

fn any<T, R: Range<T>>(r: &mut R) -> ParseResult<bool, R> {
    if r.empty() {
        Err(ParseContext::new(r.save()))
    } else {
        r.pop_front();
        Ok(true)
    }
}

#[test]
fn any_test() {
    let src = "test";
    let mut r: &[char] = &(src.chars().collect::<Vec<_>>());
    assert!(any(&mut r).is_ok());
    assert_eq!(*r.front(), 'e');

    let src = "";
    let mut r: &[char] = &(src.chars().collect::<Vec<_>>());
    assert!(any(&mut r).is_err());
}

fn exact<T: PartialEq, R: Range<T>>(t: T, r: &mut R) -> ParseResult<bool, R> {
    if !r.empty() && *r.front() == t {
        r.pop_front();
        Ok(true)
    } else {
        Err(ParseContext::new(r.save()))
    }
}

#[test]
fn exact_test() {
    let src = "test";
    let mut r : &[char] = &(from_str(src));
    assert!(exact('t', &mut r).unwrap());
    assert_eq!(*r.front(), 'e');
}

fn end<T, R: Range<T>>(r: &R) -> ParseResult<bool, R> {
    if r.empty() {
        Ok(true)
    } else {
        Err(ParseContext::new(r.save()))
    }
}

#[test]
fn end_test() {
    let r : &[char] = &(from_str(""));
    assert!(end(&r).unwrap());
}

fn string<R: Range<char>>(s: &str, src: &mut R) -> ParseResult<bool, R> {
    let before = src.save();
    for c in s.chars() {
        if src.empty() || *src.front() != c {
            return Err(ParseContext::new(before));
        }
        src.pop_front();
    }
    Ok(true)
}

#[test]
fn string_test() {
    let mut r : &[char] = &(from_str("test"));
    assert!(string("tes", &mut r).unwrap());
    assert!(exact('t', &mut r).unwrap());
    assert!(end(&r).unwrap());

    let mut r : &[char] = &(from_str("test"));
    let res = string("ex", &mut r);
    assert!(res.is_err());
    assert_eq!(res.unwrap_err().ctx, &['t', 'e', 's', 't']);
}

fn set<T: Clone + PartialEq, R: Range<T>>(ss: &[T], src: &mut R) -> ParseResult<T, R> {
    if src.empty() {
        return Err(ParseContext::new(src.save()));
    }
    for c in ss {
        if src.front() == c {
            src.pop_front();
            return Ok(c.clone());
        }
    }
    Err(ParseContext::new(src.save()))
}

#[test]
fn set_test() {
    let ss = "aiueo".chars().collect::<Vec<_>>();
    let mut src: &[char] = &(from_str("ue"));
    assert_eq!(set(&ss, &mut src).unwrap(), 'u');
    assert_eq!(src, &['e']);
}

fn range<T: PartialOrd + Clone, R: Range<T>>(s1: &T, s2: &T, src: &mut R) -> ParseResult<T, R> {
    assert!(s1 < s2);
    if src.empty() {
        return Err(ParseContext::new(src.save()));
    }
    let front = src.front().clone();
    if s1 <= &front && &front < s2 {
        src.pop_front();
        Ok(front)
    } else {
        Err(ParseContext::new(src.save()))
    }
}

#[test]
fn range_test() {
    let s1 = 'a';
    let s2 = 'e';
    let mut src : &[char] = &(from_str("compile"));
    assert_eq!(range(&s1, &s2, &mut src).unwrap(), 'c');
}

fn main() {
    let mut v: &[isize] = &[1, 2, 3, 4];
    let mut v2 = v.save();
    v.pop_front();
    println!("{:?}", v);
    println!("{:?}", v2);
    println!("Hello, world!");
}
