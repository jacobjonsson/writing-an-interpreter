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
    BlockStatement(BlockStatement),
}

#[derive(Debug, PartialEq, Clone)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
}

// TODO: We should prob implement print on each node instead,
// then we can just call each node impl from within the enum impl.
impl Print for BlockStatement {
    fn print(&self) -> String {
        let mut word = String::new();
        for statement in &self.statements {
            word.push_str(&statement.print());
        }
        return word;
    }
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
            Statement::BlockStatement(s) => s.print(),
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
    IfExpression(IfExpression),
    FunctionLiteral(FunctionLiteral),

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
            Expression::IfExpression(e) => {
                let mut s = String::new();
                s.push_str(&format!(
                    "if {} {}",
                    e.condition.print(),
                    e.consequence.print()
                ));
                if let Some(alternate) = e.alternate.as_ref() {
                    s.push_str(&alternate.print());
                }

                return s;
            }
            Expression::FunctionLiteral(f) => f.print(),
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

#[derive(Debug, PartialEq, Clone)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
    pub consequence: Box<BlockStatement>,
    pub alternate: Option<Box<BlockStatement>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionLiteral {
    pub token: Token,
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

impl Print for FunctionLiteral {
    fn print(&self) -> String {
        let mut params: Vec<String> = vec![];
        for param in &self.parameters {
            params.push(param.print());
        }

        return format!(
            "{} ({}) {}",
            self.token.token_literal(),
            params.join(","),
            self.body.print()
        );
    }
}
