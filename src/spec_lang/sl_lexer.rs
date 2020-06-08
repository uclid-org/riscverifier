use regex::Regex;
use std::str::CharIndices;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub location: usize,
    pub code: ErrorCode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorCode {
    UnrecognizedToken,
}

fn error<T>(c: ErrorCode, l: usize) -> Result<T, LexError> {
    Err(LexError {
        location: l,
        code: c,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok<'input> {
    // Dummy value
    Nil,
    // Keywords;
    Ensures,
    Requires,
    Modifies,
    Track,
    Fun,
    True,
    False,
    Old,
    Forall,
    Exists,
    // Identifier:
    Id(&'input str),
    // Primitives:
    Int(i64),
    Bv { value: u64, width: u16 },
    Bool(bool),
    // Types:
    BvType(u16),
    // Symbols:
    Colon,        // :
    ColonColon,   // ::
    Semi,         // ;
    Comma,        // ,
    Dot,          // .
    Equals,       // =
    GreaterThan,  // >
    LessThan,     // <
    Plus,         // +
    Minus,        // -
    Question,     // ?
    Asterisk,     // *
    Slash,        // /
    Ampersand,    // &
    Tilde,        // ~
    Bang,         // !
    Caret,        // ^
    Dollar,       // $
    LeftBrace,    // {
    LeftBracket,  // [
    LeftParen,    // (
    RightBrace,   // }
    RightBracket, // ]
    RightParen,   // )
}

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

const KEYWORDS: &'static [(&'static str, Tok<'static>)] = &[
    ("ensures", Tok::Ensures),
    ("requires", Tok::Requires),
    ("modifies", Tok::Modifies),
    ("track", Tok::Track),
    ("fun", Tok::Fun),
    ("false", Tok::False),
    ("true", Tok::True),
    ("old", Tok::Old),
    ("forall", Tok::Forall),
    ("exists", Tok::Exists),
];

const BOOL_KEYWORDS: &'static [(&'static str, Tok<'static>)] =
    &[("$tt", Tok::Bool(true)), ("$ff", Tok::Bool(false))];

pub struct Lexer<'input> {
    chars: std::iter::Peekable<CharIndices<'input>>,
    input: &'input str,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            chars: input.char_indices().peekable(),
            input,
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Tok<'input>, usize, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        fn identify<'input>(
            input: &'input str,
            start: usize,
            end: usize,
            // FIXME: Return value should be Self::Item but the type defined above is not in scope
            //        for internal functions. How can we write this more cleanly?
        ) -> Option<Spanned<Tok<'input>, usize, LexError>> {
            let word = &input[start..end];
            // Return keywords first
            if let Some((_, tok)) = KEYWORDS.iter().find(|kv| kv.0 == word) {
                return Some(Ok((start, tok.clone(), end)));
            }
            // Unique keywords for boolean types
            // Note that this is different from true and false (T/F)
            // in logic. This refers to the T/F values from the theory.
            // The logic T/F symbols are part of KEYWORDS above.
            if let Some((_, tok)) = BOOL_KEYWORDS.iter().find(|kv| kv.0 == word) {
                return Some(Ok((start, tok.clone(), end)));
            }
            // Convert integer numbers
            if let Ok(i) = word.parse::<i64>() {
                return Some(Ok((start, Tok::Int(i), end)));
            }
            // Convert types
            if Regex::new(r"^bv[0-9]+").unwrap().is_match(word) {
                let split = word.split("bv").collect::<Vec<&'input str>>();
                let width = split[1].parse::<u64>().unwrap();
                return Some(Ok((start, Tok::BvType(width as u16), end)));
            }
            // Convert bitvectors
            if Regex::new(r"^[0-9]+bv[0-9]+").unwrap().is_match(word) {
                let split: Vec<u64> = word
                    .split("bv")
                    .map(|num_str| num_str.parse::<u64>().unwrap())
                    .collect();
                let value = split[0];
                let width = split[1] as u16;
                return Some(Ok((start, Tok::Bv { value, width }, end)));
            }
            // Check if it's as an identifier
            // This would be for function names, variables, etc
            if Regex::new(r"^[[:alpha:]]\w*").unwrap().is_match(word) {
                return Some(Ok((start, Tok::Id(word), end)));
            }
            // Invalid token
            // TODO: Return more informative error message
            Some(error(ErrorCode::UnrecognizedToken, start))
        };
        loop {
            match self.chars.next() {
                Some((_, ' ')) | Some((_, '\n')) | Some((_, '\t')) => continue,
                Some((i, ':')) => {
                    if let Some((_, ':')) = self.chars.peek() {
                        self.chars.next();
                        return Some(Ok((i, Tok::ColonColon, i + 1))); // ::
                    } else {
                        return Some(Ok((i, Tok::Colon, i + 1))); // :
                    }
                }
                Some((i, ';')) => return Some(Ok((i, Tok::Semi, i + 1))), // ;
                Some((i, ',')) => return Some(Ok((i, Tok::Comma, i + 1))), // ,
                Some((i, '.')) => return Some(Ok((i, Tok::Dot, i + 1))),  // .
                Some((i, '=')) => return Some(Ok((i, Tok::Equals, i + 1))), // =
                Some((i, '>')) => return Some(Ok((i, Tok::GreaterThan, i + 1))), // >
                Some((i, '<')) => return Some(Ok((i, Tok::LessThan, i + 1))), // <
                Some((i, '+')) => return Some(Ok((i, Tok::Plus, i + 1))), // +
                Some((i, '-')) => return Some(Ok((i, Tok::Minus, i + 1))), // -
                Some((i, '?')) => return Some(Ok((i, Tok::Question, i + 1))), // ?
                Some((i, '*')) => return Some(Ok((i, Tok::Asterisk, i + 1))), // *
                Some((i, '/')) => return Some(Ok((i, Tok::Slash, i + 1))), // *
                Some((i, '&')) => return Some(Ok((i, Tok::Ampersand, i + 1))), // &
                Some((i, '~')) => return Some(Ok((i, Tok::Tilde, i + 1))), // ~
                Some((i, '!')) => return Some(Ok((i, Tok::Bang, i + 1))), // !
                Some((i, '^')) => return Some(Ok((i, Tok::Caret, i + 1))), // ^
                Some((i, '$')) => return Some(Ok((i, Tok::Dollar, i + 1))), // $
                Some((i, '{')) => return Some(Ok((i, Tok::LeftBrace, i + 1))), // {
                Some((i, '[')) => return Some(Ok((i, Tok::LeftBracket, i + 1))), // [
                Some((i, '(')) => return Some(Ok((i, Tok::LeftParen, i + 1))), // (
                Some((i, '}')) => return Some(Ok((i, Tok::RightBrace, i + 1))), // }
                Some((i, ']')) => return Some(Ok((i, Tok::RightBracket, i + 1))), // ]
                Some((i, ')')) => return Some(Ok((i, Tok::RightParen, i + 1))), // )
                None => return None,                                      // End of file
                Some((i, _)) => loop {
                    match self.chars.peek() {
                        Some((j, ' ')) | Some((j, ':')) | Some((j, ';')) | Some((j, ','))
                        | Some((j, '.')) | Some((j, '=')) | Some((j, '>')) | Some((j, '<'))
                        | Some((j, '+')) | Some((j, '-')) | Some((j, '?')) | Some((j, '*'))
                        | Some((j, '/')) | Some((j, '&')) | Some((j, '~')) | Some((j, '!'))
                        | Some((j, '^')) | Some((j, '$')) | Some((j, '{')) | Some((j, '['))
                        | Some((j, '(')) | Some((j, '}')) | Some((j, ']')) | Some((j, ')')) => {
                            return identify(&self.input, i, *j)
                        }
                        None => return identify(&self.input, i, self.input.len()),
                        _ => {}
                    }
                    self.chars.next();
                },
            }
        }
    }
}
