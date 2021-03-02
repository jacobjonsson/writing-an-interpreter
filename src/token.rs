#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    /// TODO: Should be Result<..>
    Illegal,
    /// TODO: Should be Option<..>
    Eof,

    Identifier {
        value: String,
    },
    Integer {
        value: String,
    },

    /// Operators
    /// =
    Assign,
    /// +
    Plus,
    /// -
    Minus,
    /// !
    Bang,
    /// *
    Asterisk,
    /// /
    Slash,

    /// ,
    Comma,
    /// ;
    Semicolon,
    /// (
    LeftParen,
    /// )
    RightParen,
    /// {
    LeftBrace,
    /// }
    RightBrace,
    /// >
    GreaterThan,
    /// <
    LessThan,
    /// ==
    Equals,
    /// !=
    NotEquals,

    /// Keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

pub fn lookup_identifier(identifier: &str) -> Token {
    match identifier {
        "fn" => Token::Function,
        "let" => Token::Let,
        "if" => Token::If,
        "else" => Token::Else,
        "true" => Token::True,
        "false" => Token::False,
        "return" => Token::Return,
        _ => Token::Identifier {
            value: identifier.into(),
        },
    }
}
