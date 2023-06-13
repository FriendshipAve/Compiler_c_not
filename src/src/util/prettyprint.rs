use std::fmt::{write, Display, Error, Formatter};

pub fn tab_align(f: &mut Formatter, numtab: usize) -> Result<(), Error> {
  write!(f, "{:1$}", "", numtab)
}

/// Given a list t1, t2, ..., tn, prints them with spacing char c.
pub fn lst_print<T>(f: &mut Formatter, lst: &[T], c: &str) -> Result<(), Error>
where
  T: Display,
{
  if lst.is_empty() {
    return Ok(());
  }
  let n = lst.len();
  let (body, tail) = (&lst[..n - 1], lst.last().unwrap());
  for t in body {
    write!(f, "{}{}", t, c)?;
  }
  write!(f, "{}", tail)
}

/// Given a list, prints them in paren if nonempty.
pub fn lst_paren_if_nonempty<T>(
  f: &mut Formatter,
  lst: &[T],
  c: &str,
) -> Result<(), Error>
where
  T: Display,
{
  if lst.is_empty() {
    return Ok(());
  }
  write!(f, "(")?;
  lst_print(f, lst, c)?;
  write!(f, ")")
}
