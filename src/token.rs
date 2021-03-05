pub trait TokenLiteral {
    fn token_literal(&self) -> String;
}

pub trait TokenType {
    fn token_type(&self) -> String;
}

#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    /// TODO: Should be Result<..>
    Illegal,
    /// TODO: Should be Option<..>
    Eof,

    Identifier(String),
    Integer(String),

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

impl TokenLiteral for Token {
    fn token_literal(&self) -> String {
        match self {
            Token::Assign => "=".into(),
            Token::Asterisk => "*".into(),
            Token::Bang => "!".into(),
            Token::Comma => ",".into(),
            Token::Else => "else".into(),
            Token::Eof => "Eof".into(),
            Token::Equals => "==".into(),
            Token::False => "false".into(),
            Token::Function => "fn".into(),
            Token::GreaterThan => ">".into(),
            Token::Identifier(value) => value.clone(),
            Token::If => "if".into(),
            Token::Illegal => "Illegal".into(),
            Token::Integer(value) => value.clone(),
            Token::LeftBrace => "{".into(),
            Token::LeftParen => "(".into(),
            Token::LessThan => "<".into(),
            Token::Let => "let".into(),
            Token::Minus => "-".into(),
            Token::NotEquals => "!=".into(),
            Token::Plus => "+".into(),
            Token::Return => "return".into(),
            Token::RightBrace => "}".into(),
            Token::RightParen => ")".into(),
            Token::Semicolon => ";".into(),
            Token::Slash => "/".into(),
            Token::True => "true".into(),
        }
    }
}

impl TokenType for Token {
    fn token_type(&self) -> String {
        match self {
            Token::Assign => "assign".into(),
            Token::Asterisk => "asterisk".into(),
            Token::Bang => "bang".into(),
            Token::Comma => "comma".into(),
            Token::Else => "else".into(),
            Token::Eof => "eof".into(),
            Token::Equals => "equals".into(),
            Token::False => "false".into(),
            Token::Function => "function".into(),
            Token::GreaterThan => "greater_than".into(),
            Token::Identifier(_) => "identifier".into(),
            Token::If => "if".into(),
            Token::Illegal => "illegal".into(),
            Token::Integer(_) => "integer".into(),
            Token::LeftBrace => "left_brace".into(),
            Token::LeftParen => "left_paren".into(),
            Token::LessThan => "less_than".into(),
            Token::Let => "let".into(),
            Token::Minus => "minus".into(),
            Token::NotEquals => "not_equals".into(),
            Token::Plus => "plus".into(),
            Token::Return => "return".into(),
            Token::RightBrace => "right_brace".into(),
            Token::RightParen => "right_paren".into(),
            Token::Semicolon => "semicolon".into(),
            Token::Slash => "slash".into(),
            Token::True => "true".into(),
        }
    }
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
        _ => Token::Identifier(identifier.into()),
    }
}
