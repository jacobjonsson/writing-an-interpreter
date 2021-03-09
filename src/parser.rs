use crate::{
    ast::{
        BlockStatement, BooleanExpression, Expression, ExpressionStatement, Identifier,
        IfExpression, InfixExpression, IntegerLiteral, LetStatement, PrefixExpression, Program,
        ReturnStatement, Statement,
    },
    lexer::Lexer,
    token::{Token, TokenLiteral},
};

pub struct ParserError(String);

#[derive(Debug, PartialEq, PartialOrd)]
enum OperatorPrecedence {
    Lowest = 1,
    Equals = 2,
    LessGreater = 3,
    Sum = 4,
    Product = 6,
    Prefix = 7,
    Call = 8,
}

fn token_to_precedence(token: &Token) -> OperatorPrecedence {
    match token {
        Token::Equals => OperatorPrecedence::Equals,
        Token::NotEquals => OperatorPrecedence::Equals,
        Token::LessThan => OperatorPrecedence::LessGreater,
        Token::GreaterThan => OperatorPrecedence::LessGreater,
        Token::Plus => OperatorPrecedence::Sum,
        Token::Minus => OperatorPrecedence::Sum,
        Token::Slash => OperatorPrecedence::Product,
        Token::Asterisk => OperatorPrecedence::Product,
        _ => OperatorPrecedence::Lowest,
    }
}

pub struct Parser {
    lexer: Lexer,
    errors: Vec<String>,
    current_token: Token,
    peek_token: Token,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        let mut parser = Parser {
            lexer: lexer,
            errors: Vec::new(),
            current_token: Token::Eof,
            peek_token: Token::Eof,
        };

        parser.next_token();
        parser.next_token();
        return parser;
    }

    fn peek_precedence(&self) -> OperatorPrecedence {
        token_to_precedence(&self.peek_token)
    }

    fn current_precedence(&self) -> OperatorPrecedence {
        token_to_precedence(&self.current_token)
    }

    pub fn parse_program(&mut self) -> Program {
        let mut statements: Vec<Statement> = vec![];

        while &self.current_token != &Token::Eof {
            match self.parse_statement() {
                Ok(statement) => statements.push(statement),
                Err(err) => self.errors.push(err.0),
            };

            self.next_token();
        }

        return Program { statements };
    }

    pub fn errors(&self) -> Vec<String> {
        return self.errors.clone();
    }

    fn parse_identifer(&self) -> Expression {
        return Expression::Identifier(Identifier {
            token: self.current_token.clone(),
            value: self.current_token.token_literal(),
        });
    }

    fn peek_error(&mut self, token: Token) {
        let msg = format!(
            "Expected next token to be {:?}, got {:?} instead",
            token, self.peek_token
        );
        self.errors.push(msg);
    }

    fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        match self.current_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_return_statement(&mut self) -> Result<Statement, ParserError> {
        let token = self.current_token.clone();
        self.next_token();

        // TODO: Skipping expressions for now
        loop {
            match &self.current_token {
                Token::Semicolon => break,
                _ => self.next_token(),
            }
        }

        Ok(Statement::Return(ReturnStatement {
            token: token,
            value: Expression::Nil,
        }))
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParserError> {
        let token = self.current_token.clone();

        let expression = self.parse_expression(OperatorPrecedence::Lowest)?;

        while Token::Semicolon == self.peek_token {
            self.next_token();
        }

        return Ok(Statement::Expression(ExpressionStatement {
            expression: expression,
            token: token,
        }));
    }

    fn parser_integer_literal(&mut self) -> Result<Expression, ParserError> {
        let token = self.current_token.clone();
        let value = self
            .current_token
            .token_literal()
            .parse::<i64>()
            .map_err(|_| {
                ParserError(format!(
                    "Failed to parse {} as integer",
                    self.current_token.token_literal()
                ))
            })?;

        return Ok(Expression::IntegerLiteral(IntegerLiteral {
            token: token,
            value: value,
        }));
    }

    fn parse_expression(
        &mut self,
        precedence: OperatorPrecedence,
    ) -> Result<Expression, ParserError> {
        let mut left = self.parse_prefix()?;

        while Token::Semicolon != self.peek_token && precedence < self.peek_precedence() {
            self.next_token();

            if let Ok(s) = self.parse_infix(left.clone()) {
                left = s;
            } else {
                return Ok(left);
            }
        }

        Ok(left)
    }

    fn parse_prefix(&mut self) -> Result<Expression, ParserError> {
        match &self.current_token {
            Token::Identifier(_) => Ok(self.parse_identifer()),
            Token::Integer(_) => self.parser_integer_literal(),
            Token::Bang => self.parse_prefix_expression(),
            Token::Plus => self.parse_prefix_expression(),
            Token::Minus => self.parse_prefix_expression(),
            Token::True => self.parse_boolean(),
            Token::False => self.parse_boolean(),
            Token::LeftParen => self.parse_grouped_expression(),
            Token::If => self.parse_if_expression(),
            _ => Err(ParserError(format!(
                "No prefix parse function for {} found",
                self.current_token.token_literal()
            ))),
        }
    }

    fn parse_if_expression(&mut self) -> Result<Expression, ParserError> {
        let token = self.current_token.clone();

        self.expect_peek(Token::LeftParen)?;
        self.next_token();
        let condition = self.parse_expression(OperatorPrecedence::Lowest)?;

        self.expect_peek(Token::RightParen)?;

        self.expect_peek(Token::LeftBrace)?;

        let consequence = self.parse_block_statement()?;

        let mut alternate: Option<Box<BlockStatement>> = None;
        if self.peek_token == Token::Else {
            self.next_token();
            self.expect_peek(Token::LeftBrace)?;
            alternate = Some(Box::new(self.parse_block_statement()?));
        }

        return Ok(Expression::IfExpression(IfExpression {
            alternate: alternate,
            consequence: Box::new(consequence),
            condition: Box::new(condition),
            token: token,
        }));
    }

    fn parse_block_statement(&mut self) -> Result<BlockStatement, ParserError> {
        let token = self.current_token.clone();
        let mut statements: Vec<Statement> = vec![];

        self.next_token();

        while self.current_token != Token::RightBrace && self.current_token != Token::Eof {
            let statement = self.parse_statement()?;
            statements.push(statement);
            self.next_token();
        }

        return Ok(BlockStatement { token, statements });
    }

    fn parse_grouped_expression(&mut self) -> Result<Expression, ParserError> {
        self.next_token();

        let expression = self.parse_expression(OperatorPrecedence::Lowest);

        if Token::RightParen != self.peek_token {
            return Err(ParserError(format!(
                "Expected ) but got {:?}",
                self.peek_token
            )));
        }

        self.next_token();

        return expression;
    }

    fn parse_boolean(&mut self) -> Result<Expression, ParserError> {
        Ok(Expression::BooleanExpression(BooleanExpression {
            token: self.current_token.clone(),
            value: match &self.current_token {
                Token::True => true,
                Token::False => false,
                c => {
                    return Err(ParserError(format!(
                        "Expected to get true or false but got {:?}",
                        c
                    )))
                }
            },
        }))
    }

    fn parse_infix(&mut self, left: Expression) -> Result<Expression, ParserError> {
        match &self.current_token {
            Token::Plus => self.parse_infix_expression(left),
            Token::Minus => self.parse_infix_expression(left),
            Token::Slash => self.parse_infix_expression(left),
            Token::Asterisk => self.parse_infix_expression(left),
            Token::Equals => self.parse_infix_expression(left),
            Token::NotEquals => self.parse_infix_expression(left),
            Token::LessThan => self.parse_infix_expression(left),
            Token::GreaterThan => self.parse_infix_expression(left),
            t => Err(ParserError(format!(
                "No infix parse function for {} found",
                t.token_literal()
            ))),
        }
    }

    fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression, ParserError> {
        let token = self.current_token.clone();
        let operator = self.current_token.token_literal().clone();
        let precedence = self.current_precedence();
        self.next_token();
        let right = self.parse_expression(precedence)?;
        Ok(Expression::InfixExpression(InfixExpression {
            left: Box::new(left),
            token: token,
            operator: operator,
            right: Box::new(right),
        }))
    }

    fn parse_prefix_expression(&mut self) -> Result<Expression, ParserError> {
        let token = self.current_token.clone();
        let operator = self.current_token.token_literal();
        self.next_token();
        let right = self.parse_expression(OperatorPrecedence::Prefix)?;
        Ok(Expression::PrefixExpression(PrefixExpression {
            token,
            operator,
            right: Box::new(right),
        }))
    }

    fn parse_let_statement(&mut self) -> Result<Statement, ParserError> {
        // Next token must be identifier
        let name = Identifier {
            token: self.peek_token.clone(),
            value: self.assert_identifier()?,
        };
        self.next_token();
        self.assert_assign()?;

        // TODO: Skipping expressions for now
        loop {
            match &self.current_token {
                Token::Semicolon => break,
                _ => self.next_token(),
            }
        }

        return Ok(Statement::Let(LetStatement {
            name,
            token: Token::Let,
            value: Expression::Nil,
        }));
    }

    fn next_token(&mut self) {
        self.current_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }
}

// Token assertions
impl Parser {
    fn assert_semicolon(&self) -> Result<(), ParserError> {
        match &self.peek_token {
            Token::Semicolon => Ok(()),
            c => Err(ParserError(format!(
                "Expected ; but got: {}",
                c.token_literal()
            ))),
        }
    }

    fn assert_assign(&self) -> Result<(), ParserError> {
        match &self.peek_token {
            Token::Assign => Ok(()),
            c => Err(ParserError(format!(
                "Expected ; but got: {}",
                c.token_literal()
            ))),
        }
    }

    fn assert_identifier(&self) -> Result<String, ParserError> {
        match &self.peek_token {
            Token::Identifier(value) => Ok(value.clone()),
            c => Err(ParserError(format!(
                "Expected identifier but got: {}",
                c.token_literal()
            ))),
        }
    }

    fn expect_peek(&mut self, token: Token) -> Result<(), ParserError> {
        if token != self.peek_token {
            return Err(ParserError(format!(
                "Expected {:?} but got {:?}",
                token, self.peek_token
            )));
        }

        self.next_token();

        return Ok(());
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::*, token::TokenLiteral};

    use super::*;

    #[test]
    fn test_let_statements() {
        let input = "
        let x = 5;
        let y = 10;
        let foobar = 838383;
        ";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();

        check_parser_errors(&parser);

        assert_eq!(
            program.statements.len(),
            3,
            "Program should contains 3 statement"
        );

        let tests = vec!["x", "y", "foobar"];
        for (index, test) in tests.iter().enumerate() {
            let statement = &program.statements[index];
            assert_eq!(test_let_statement(statement, test), true);
        }
    }

    fn test_let_statement(statement: &Statement, expected_name: &str) -> bool {
        match statement {
            Statement::Let(statement) => {
                statement.name.token.token_literal() == String::from(expected_name)
            }
            _ => false,
        }
    }

    fn check_parser_errors(parser: &Parser) {
        let errors = parser.errors();
        if errors.len() != 0 {
            panic!("Expected parser to have no errors: {:?}", errors);
        }
    }

    #[test]
    fn test_return_statements() {
        let input = "
        return 5;
        return 10;
        return 838383;
        ";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        check_parser_errors(&parser);

        assert_eq!(
            program.statements.len(),
            3,
            "Program should contains 3 statement"
        );

        for statement in &program.statements {
            match statement {
                Statement::Return { .. } => continue,
                s => panic!("Expected return got but got {:?}", s),
            }
        }
    }

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        check_parser_errors(&parser);

        assert_eq!(
            program.statements.len(),
            1,
            "Program should contain 1 statement"
        );

        let statement = match &program.statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but got {:?}", s),
        };

        let identifier = match &statement.expression {
            Expression::Identifier(s) => s,
            s => panic!("Expected identifier but got {:?}", s),
        };

        assert_eq!(
            identifier.value,
            String::from("foobar"),
            "Values should match"
        );
    }

    #[test]
    fn test_integer_literal_expression() {
        let input = "5;";

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        check_parser_errors(&parser);

        assert_eq!(
            program.statements.len(),
            1,
            "Program should contain 1 statement"
        );

        let statement = match &program.statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but got {:?}", s),
        };

        let integer = match &statement.expression {
            Expression::IntegerLiteral(s) => s,
            s => panic!("Expected integer literal but got {:?}", s),
        };

        assert_eq!(integer.value, 5, "Values should match");
    }

    #[test]
    fn test_prefix_expression() {
        let tests = vec![
            ("!5;", "!", Expected::Integer(5)),
            ("-15;", "-", Expected::Integer(15)),
            ("!true", "!", Expected::Boolean(true)),
            ("!false", "!", Expected::Boolean(false)),
        ];

        for test in tests {
            let lexer = Lexer::new(test.0);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();
            check_parser_errors(&parser);

            assert_eq!(
                program.statements.len(),
                1,
                "Program statements should be 1"
            );

            let statement = match &program.statements[0] {
                Statement::Expression(statement) => statement,
                _ => panic!("Expected expression statement but did not get it"),
            };

            let prefix_expression = match &statement.expression {
                Expression::PrefixExpression(prefix_expression) => prefix_expression,
                _ => panic!("Expected prefix expression but did not get it"),
            };

            assert_eq!(prefix_expression.operator, test.1);
            test_literal_expression(prefix_expression.right.as_ref(), test.2);
        }
    }

    enum Expected {
        String(String),
        Integer(i64),
        Boolean(bool),
    }

    fn test_literal_expression(expression: &Expression, value: Expected) {
        match value {
            Expected::String(v) => test_identifier(expression, v),
            Expected::Integer(v) => test_integer_literal(expression, v),
            Expected::Boolean(v) => test_boolean_literal(expression, v),
        }
    }

    fn test_integer_literal(expression: &Expression, value: i64) {
        let integer = match expression {
            Expression::IntegerLiteral(v) => v,
            e => panic!("Expected integer literal but did got {:?}", e),
        };

        assert_eq!(integer.value, value, "Values should match");
        assert_eq!(
            integer.token.token_literal(),
            value.to_string(),
            "Token literals should match"
        )
    }

    fn test_boolean_literal(expression: &Expression, value: bool) {
        let literal = match expression {
            Expression::BooleanExpression(v) => v,
            e => panic!("Expected boolean identifier but got {:?}", e),
        };

        assert_eq!(literal.value, value);
        assert_eq!(literal.token.token_literal(), value.to_string());
    }

    fn test_identifier(expression: &Expression, value: String) {
        let identifier = match expression {
            Expression::Identifier(v) => v,
            e => panic!("Expected identifier but got {:?}", e),
        };

        assert_eq!(identifier.value, value);
        assert_eq!(identifier.token.token_literal(), value);
    }

    fn test_infix_expression(
        expression: &Expression,
        left: Expected,
        operator: &str,
        right: Expected,
    ) {
        let infix_expression = match expression {
            Expression::InfixExpression(e) => e,
            e => panic!("Expected infix expression but got {:?}", e),
        };

        test_literal_expression(&infix_expression.left, left);
        assert_eq!(
            infix_expression.operator, operator,
            "Operators should match"
        );
        test_literal_expression(&infix_expression.right, right);
    }

    #[test]
    fn test_infix_expressions() {
        let tests = vec![
            ("5 + 5;", Expected::Integer(5), "+", Expected::Integer(5)),
            ("5 - 5;", Expected::Integer(5), "-", Expected::Integer(5)),
            ("5 * 5;", Expected::Integer(5), "*", Expected::Integer(5)),
            ("5 / 5;", Expected::Integer(5), "/", Expected::Integer(5)),
            ("5 > 5;", Expected::Integer(5), ">", Expected::Integer(5)),
            ("5 < 5;", Expected::Integer(5), "<", Expected::Integer(5)),
            ("5 == 5;", Expected::Integer(5), "==", Expected::Integer(5)),
            ("5 != 5;", Expected::Integer(5), "!=", Expected::Integer(5)),
            (
                "true == true;",
                Expected::Boolean(true),
                "==",
                Expected::Boolean(true),
            ),
            (
                "true != false;",
                Expected::Boolean(true),
                "!=",
                Expected::Boolean(false),
            ),
            (
                "false == false;",
                Expected::Boolean(false),
                "==",
                Expected::Boolean(false),
            ),
        ];

        for test in tests {
            let lexer = Lexer::new(test.0);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();
            check_parser_errors(&parser);

            assert_eq!(
                program.statements.len(),
                1,
                "Program should contain one statement"
            );

            let statement = match &program.statements[0] {
                Statement::Expression(s) => s,
                s => panic!("Expected expression statement but got {:?}", s),
            };

            test_infix_expression(&statement.expression, test.1, test.2, test.3);
        }
    }

    #[test]
    fn test_operator_precedence_parsing() {
        let tests = vec![
            ("5 + 5", "(5 + 5)"),
            ("true", "true"),
            ("false", "false"),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b / c", "(a + (b / c))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
        ];

        for test in tests {
            let lexer = Lexer::new(test.0);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();
            check_parser_errors(&parser);

            let actual = program.print();
            assert_eq!(actual, test.1);
        }
    }

    #[test]
    fn test_boolean_expression() {
        let tests = vec![("true;", true), ("false;", false)];

        for test in tests {
            let lexer = Lexer::new(test.0);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();
            check_parser_errors(&parser);

            assert_eq!(
                program.statements.len(),
                1,
                "Program should contain one statement"
            );

            let statement = match &program.statements[0] {
                Statement::Expression(s) => s,
                s => panic!(
                    "Statement should be an expression statement but got {:?}",
                    s
                ),
            };

            let expression = match &statement.expression {
                Expression::BooleanExpression(e) => e,
                e => panic!("Expression should be boolean expression but got {:?}", e),
            };

            assert_eq!(expression.value, test.1, "Values should match");
        }
    }

    #[test]
    fn test_if_expression() {
        let input = "if (x < y) { x }";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 1);
        let statement = match &program.statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but got {:?}", s),
        };

        let expression = match &statement.expression {
            Expression::IfExpression(e) => e,
            e => panic!("Expected if expression but got {:?}", e),
        };

        test_infix_expression(
            expression.condition.as_ref(),
            Expected::String("x".into()),
            "<",
            Expected::String("y".into()),
        );

        let consequence = match &expression.consequence.statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but {:?}", s),
        };

        test_identifier(&consequence.expression, "x".into());

        if let Some(alternate) = &expression.alternate {
            panic!("Expected alternate to be None but got {:?}", alternate);
        }
    }

    #[test]
    fn test_if_else_expression() {
        let input = "if (x < y) { x } else { y  }";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        check_parser_errors(&parser);

        assert_eq!(program.statements.len(), 1);
        let statement = match &program.statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but got {:?}", s),
        };

        let expression = match &statement.expression {
            Expression::IfExpression(e) => e,
            e => panic!("Expected if expression but got {:?}", e),
        };

        test_infix_expression(
            expression.condition.as_ref(),
            Expected::String("x".into()),
            "<",
            Expected::String("y".into()),
        );

        let consequence = match &expression.consequence.statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but {:?}", s),
        };

        test_identifier(&consequence.expression, "x".into());

        if let None = &expression.alternate {
            panic!("Expected alternate to be Some but got None");
        }

        let alternate = match &expression.alternate {
            Some(a) => a,
            None => panic!("Expected alternate to be defined but got None"),
        };

        let statements = match &alternate.as_ref().statements[0] {
            Statement::Expression(s) => s,
            s => panic!("Expected expression statement but {:?}", s),
        };

        test_identifier(&statements.expression, "y".into());
    }
}
