use crate::{lexer::Lexer, token::Token};
use std::io::{self, Write};

pub fn start() {
    loop {
        let mut line = String::new();
        print!(">>> ");
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut line).unwrap();

        let mut lexer = Lexer::new(&line);
        loop {
            let token = lexer.next_token();
            if token != Token::Eof {
                println!("{:?}", token);
                continue;
            } else {
                break;
            }
        }
    }
}
