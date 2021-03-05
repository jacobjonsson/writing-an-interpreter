#![allow(dead_code)]
mod ast;
mod lexer;
mod parser;
mod repl;
mod token;

fn main() {
    repl::start();
}
