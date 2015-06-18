#![crate_name = "rparse"]
#![deny(missing_docs)]

//! A parser combinator library.
//! This library can work with the iterators that's element is of your own type.

pub mod prim;
pub mod combinator;

#[cfg(test)]
mod tests {
    use prim::*;
    use combinator::*;
    use std::iter::{Iterator};

    #[test]
    fn digits_test() {
        let non_z = ['1', '2', '3', '4', '5', '6', '7', '8', '9'];
        let non_zero = set(&non_z);
        let digit = select(exact('0'), non_zero.clone());
        let dig_head = seq(seq(non_zero, option(digit.clone())), option(digit.clone()));
        let dig_tail = seq(seq(seq(exact(','), digit.clone()), digit.clone()), digit);
        let zero = success(seq(exact('0'), end()));
        let mut digits = select(success(zero), success(seq(seq(dig_head, many(dig_tail)), end())));

        for s in ["0", "1", "1,234"].iter() {
            let src = s.chars().peekable();
            let ret = digits.parse(src);
            assert!(ret.is_ok());
            if let Ok(((), mut ctx)) = ret {
                assert!(ctx.peek().is_none());
            }
        }
    }

    #[test]
    fn combi_test() {
        let ss = ['a', 'b', 'c'];
        let res = set(&ss).map(|c| format!("({})", c))
                          .parse("cat".chars().peekable());
        assert!(res.is_ok());
        if let Ok((r, ctx)) = res {
            assert_eq!("(c)", r);
            assert_eq!(vec!['a', 't'], ctx.collect::<Vec<_>>());
        }
    }
}
