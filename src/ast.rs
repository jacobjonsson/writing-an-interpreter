use crate::token::{Token, TokenLiteral};

pub trait Print {
    fn print(&self) -> String;
}

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Print for Program {
    fn print(&self) -> String {
        let mut program = String::new();
        for statement in &self.statements {
            program.push_str(&statement.print());
        }
        return program;
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl Print for Statement {
    fn print(&self) -> String {
        match self {
            Statement::Expression(s) => format!("{}", s.expression.print()),
            Statement::Let(s) => format!(
                "{} {} = {};",
                s.token.token_literal(),
                s.name.print(),
                s.value.print()
            ),
            Statement::Return(s) => format!("{} {};", s.token.token_literal(), s.value.print()),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ReturnStatement {
    pub token: Token,
    pub value: Expression,
}
#[derive(Debug, PartialEq, Clone)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Identifier {
    pub token: Token,
    pub value: String,
}

impl Print for Identifier {
    fn print(&self) -> String {
        self.value.clone()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Identifier(Identifier),
    IntegerLiteral(IntegerLiteral),
    PrefixExpression(PrefixExpression),
    InfixExpression(InfixExpression),
    BooleanExpression(BooleanExpression),

    // TODO: Keeping this here for now
    Nil,
}

impl Print for Expression {
    fn print(&self) -> String {
        match &self {
            Expression::Identifier(e) => e.print(),
            Expression::IntegerLiteral(e) => format!("{}", e.value),
            Expression::PrefixExpression(e) => format!("({}{})", e.operator, e.right.print()),
            Expression::InfixExpression(e) => {
                format!("({} {} {})", e.left.print(), e.operator, e.right.print())
            }
            Expression::BooleanExpression(e) => format!("{}", e.value),
            Expression::Nil => String::new(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

#[derive(Debug, PartialEq, Clone)]
pub struct PrefixExpression {
    pub token: Token,
    pub operator: String,
    pub right: Box<Expression>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub operator: String,
    pub right: Box<Expression>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct BooleanExpression {
    pub token: Token,
    pub value: bool,
}
