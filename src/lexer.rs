use crate::token::{lookup_identifier, Token};

pub struct Lexer {
    input: String,
    position: usize,      // current position in input (points to current
    read_position: usize, // current reading position in the input
    ch: Option<char>,
}

impl Lexer {
    pub fn new(input: &str) -> Lexer {
        let mut lexer = Lexer {
            input: input.into(),
            position: 0,
            read_position: 0,
            ch: input.chars().nth(0),
        };

        lexer.read_char();
        return lexer;
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let char = match self.ch {
            Some(v) => v,
            None => return Token::Eof,
        };

        let token = match char {
            ';' => Token::Semicolon,
            '(' => Token::LeftParen,
            ')' => Token::RightParen,
            '{' => Token::LeftBrace,
            '}' => Token::RightBrace,
            ',' => Token::Comma,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '/' => Token::Slash,
            '*' => Token::Asterisk,
            '<' => Token::LessThan,
            '>' => Token::GreaterThan,
            '=' => {
                if self.peek_char() == Some('=') {
                    self.read_char();
                    Token::Equals
                } else {
                    Token::Assign
                }
            }
            '!' => {
                if self.peek_char() == Some('=') {
                    self.read_char();
                    Token::NotEquals
                } else {
                    Token::Bang
                }
            }
            c if Lexer::is_letter(c) => {
                let identifier = self.read_identifier();
                return lookup_identifier(&identifier);
            }

            c if Lexer::is_digit(c) => {
                let number = self.read_number();
                return Token::Integer(number);
            }

            _ => Token::Illegal,
        };

        self.read_char();
        return token;
    }

    fn peek_char(&self) -> Option<char> {
        return self.input.chars().nth(self.read_position);
    }

    fn read_identifier(&mut self) -> String {
        let mut word = String::new();
        while let Some(ch) = self.ch {
            if Lexer::is_letter(ch) {
                word.push(ch);
                self.read_char();
            } else {
                break;
            }
        }
        return word;
    }

    fn read_number(&mut self) -> String {
        let mut number = String::new();
        while let Some(ch) = self.ch {
            if Lexer::is_digit(ch) {
                number.push(ch);
                self.read_char();
            } else {
                break;
            }
        }
        return number;
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.ch {
            if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' {
                self.read_char();
            } else {
                break;
            }
        }
    }

    fn read_char(&mut self) {
        if self.read_position > self.input.len() {
            self.ch = None;
        } else {
            self.ch = self.input.chars().nth(self.read_position);
        }
        self.position = self.read_position;
        self.read_position += 1;
    }

    fn is_letter(ch: char) -> bool {
        return ch.is_alphabetic() || ch == '_';
    }

    fn is_digit(ch: char) -> bool {
        return ch.is_numeric();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token() {
        let tests = vec![
            (Token::Let, "let"),
            (Token::Identifier("five".into()), "five"),
            (Token::Assign, "="),
            (Token::Integer("5".into()), "5"),
            (Token::Semicolon, ";"),
            (Token::Let, "let"),
            (Token::Identifier("ten".into()), "ten"),
            (Token::Assign, "="),
            (Token::Integer("10".into()), "10"),
            (Token::Semicolon, ";"),
            (Token::Let, "let"),
            (Token::Identifier("add".into()), "add"),
            (Token::Assign, "="),
            (Token::Function, "fn"),
            (Token::LeftParen, "("),
            (Token::Identifier("x".into()), "x"),
            (Token::Comma, ","),
            (Token::Identifier("y".into()), "y"),
            (Token::RightParen, ")"),
            (Token::LeftBrace, "{"),
            (Token::Identifier("x".into()), "x"),
            (Token::Plus, "+"),
            (Token::Identifier("y".into()), "y"),
            (Token::Semicolon, ";"),
            (Token::RightBrace, "}"),
            (Token::Semicolon, ";"),
            (Token::Let, "let"),
            (Token::Identifier("result".into()), "result"),
            (Token::Assign, "="),
            (Token::Identifier("add".into()), "add"),
            (Token::LeftParen, "("),
            (Token::Identifier("five".into()), "five"),
            (Token::Comma, ","),
            (Token::Identifier("ten".into()), "ten"),
            (Token::RightParen, ")"),
            (Token::Semicolon, ";"),
            (Token::Bang, "!"),
            (Token::Minus, "-"),
            (Token::Slash, "/"),
            (Token::Asterisk, "*"),
            (Token::Integer("5".into()), "5"),
            (Token::Semicolon, ";"),
            (Token::Integer("5".into()), "5"),
            (Token::LessThan, "<"),
            (Token::Integer("10".into()), "10"),
            (Token::GreaterThan, ">"),
            (Token::Integer("5".into()), "5"),
            (Token::Semicolon, ";"),
            (Token::If, "if"),
            (Token::LeftParen, "("),
            (Token::Integer("5".into()), "5"),
            (Token::LessThan, "<"),
            (Token::Integer("10".into()), "10"),
            (Token::RightParen, ")"),
            (Token::LeftBrace, "{"),
            (Token::Return, "return"),
            (Token::True, "true"),
            (Token::Semicolon, ";"),
            (Token::RightBrace, "}"),
            (Token::Else, "else"),
            (Token::LeftBrace, "{"),
            (Token::Return, "return"),
            (Token::False, "false"),
            (Token::Semicolon, ";"),
            (Token::RightBrace, "}"),
            (Token::Integer("10".into()), "10"),
            (Token::Equals, "=="),
            (Token::Integer("10".into()), "10"),
            (Token::Semicolon, ";"),
            (Token::Integer("10".into()), "10"),
            (Token::NotEquals, "!="),
            (Token::Integer("9".into()), "9"),
            (Token::Semicolon, ";"),
            (Token::Eof, ""),
        ];

        let input = "let five = 5;
        let ten = 10;

        let add = fn(x, y) {
            x + y;
        };

        let result = add(five, ten);
        !-/*5;
        5 < 10 > 5;

        if (5 < 10) {
            return true;
        } else {
            return false;
        }

        10 == 10;
        10 != 9;
        ";

        let mut lexer = Lexer::new(input);

        for test in tests {
            let token = lexer.next_token();

            assert_eq!(test.0, token);
        }
    }
}
