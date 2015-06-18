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
