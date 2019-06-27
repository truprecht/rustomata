pub enum ParseResult<A, B> {
    Ok(A),
    Fallback(B),
    None,
}

impl<A, B> ParseResult<A, B> {
    pub fn as_option(self) -> Option<A> {
        match self {
            ParseResult::Ok(t) => Some(t),
            _ => None,
        }
    }

    pub fn map_ok<R, F: FnOnce(A) -> R>(self, f: F) -> ParseResult<R, B> {
        match self {
            ParseResult::Ok(t) => ParseResult::Ok(f(t)),
            ParseResult::Fallback(t) => ParseResult::Fallback(t),
            ParseResult::None => ParseResult::None,
        }
    }

    pub fn map_fallback<R, F: FnOnce(B) -> R>(self, f: F) -> ParseResult<A, R> {
        match self {
            ParseResult::Ok(t) => ParseResult::Ok(t),
            ParseResult::Fallback(t) => ParseResult::Fallback(f(t)),
            ParseResult::None => ParseResult::None,
        }
    }
}

impl<A, B> Iterator for ParseResult<A, B>
where
    A: Iterator,
    B: Iterator<Item = A::Item>,
{
    type Item = A::Item;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut ParseResult::Ok(ref mut a) => a.next(),
            &mut ParseResult::Fallback(ref mut b) => b.next(),
            &mut ParseResult::None => None,
        }
    }
}
