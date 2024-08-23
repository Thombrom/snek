use logos::Logos;

use crate::error::SnekError;


#[derive(Debug, Logos)]
#[logos(skip r"[ \t\r\n\f]+")]
enum Token<'a> {
    #[token("(")]
    LeftParen,

    #[token(")")]
    RightParen,

    #[regex(r#"[\w+0-9.*/!+^#><=?-]+"#, |lex| lex.slice())]
    Literal(&'a str),
}

#[derive(Debug, PartialEq)]
pub enum Literal<'a> {
    Identifier(&'a str),
    Number(f64),
}

// Sexps are the basic building blocks of snek
#[derive(Debug, PartialEq)]
pub enum Sexp<'a> {
    Atom(Literal<'a>),
    Expression(Vec<Self>)
}

type ParseResult<O> = Result<O, SnekError>;


fn lexer<'a>(input: &'a str)  -> ParseResult<Vec<Token<'a>>> {
    let mut tokens = vec![];
    let mut tokenizer = Token::lexer(input);
    
    while let Some(result) = tokenizer.next() {
        match result {
            Ok(token) => tokens.push(token),
            Err(_) => return Err(SnekError::SnekSyntaxError)
        }
    } 

    Ok(tokens)
}

fn parse_token<'a, 'b: 'a>(token_recognizer: impl Fn(&'a Token<'b>) -> bool) -> impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], &'a Token<'b>)> {
    move |tokens| {
        if tokens.len() == 0 { return Err(SnekError::SnekSyntaxError); }

        if !token_recognizer(&tokens[0]) { return Err(SnekError::SnekSyntaxError) }
        Ok((&tokens[1..], &tokens[0]))
    }
}

fn parse_surrounds<'a, 'b: 'a, O>(
    start_recognizer: impl Fn(&'a Token<'b>) -> bool,
    internal_parser: impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)>,
    end_recognizer: impl Fn(&'a Token<'b>) -> bool,
) -> impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)> {
    let start_parser = parse_token(start_recognizer);
    let end_parser = parse_token(end_recognizer);

    move |tokens| {
        let (tokens, _) = start_parser(tokens)?;
        let (tokens, internal) = internal_parser(tokens)?;
        let (tokens, _) = end_parser(tokens)?;

        Ok((tokens, internal))
    }
}

fn parse_list<'a, 'b: 'a, O>(
    parser: impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)>
) -> impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], Vec<O>)> {
    move |mut tokens| {
        let mut result = vec![];

        while let Ok((new_tokens, value)) = parser(tokens) {
            result.push(value);
            tokens = new_tokens
        }

        Ok((tokens, result))
    }
}

fn parse_either<'a, 'b: 'a, O>(
    a: impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)>,
    b: impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)>,
) -> impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)> {
    move |tokens| {
        if let Ok(a) = a(tokens) {
            return Ok(a)
        }
        b(tokens)
    }

}

fn parser_map<'a, 'b: 'a, I, O>(
    parser: impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], I)>,
    f: impl Fn(I) -> O
) -> impl Fn(&'a [Token<'b>]) -> ParseResult<(&'a [Token<'b>], O)> {
    move |tokens| {
        let (tokens, value) = parser(tokens)?;
        Ok((tokens, f(value)))
    }
}

fn parse_atom<'a, 'b: 'a>(tokens: &'a[Token<'b>]) -> ParseResult<(&'a [Token<'b>], Sexp<'b>)> {
    let (tokens, literal) = parse_token(|token| matches!(token, Token::Literal(_)))(tokens)?;
    let literal = match literal {
        Token::Literal(literal) => {
            if let Ok(number) = literal.parse() { Sexp::Atom(Literal::Number(number)) }
            else { Sexp::Atom(Literal::Identifier(literal))}
        }
        _ => unreachable!()
    };
    Ok((tokens, literal))
}

fn parse_expression<'a, 'b: 'a>(tokens: &'a[Token<'b>]) -> ParseResult<(&'a [Token<'b>], Sexp<'b>)> {
    parse_surrounds(
        |token| matches!(token, Token::LeftParen), 
        parser_map(
            parse_list(parse_sexp),
            |sexp_list| Sexp::Expression(sexp_list)
        ),
        |token| matches!(token, Token::RightParen)
    )(tokens)
}


fn parse_sexp<'a, 'b: 'a>(tokens: &'a[Token<'b>]) -> ParseResult<(&'a [Token<'b>], Sexp<'b>)> {
    parse_either(
        parse_atom,
        parse_expression
    )(tokens)
}

pub fn parser<'a>(input: &'a str) -> ParseResult<Sexp<'a>> {
    let tokens = lexer(input)?;

    let (tokens, sexp) = parse_sexp(&tokens)?;
    if tokens.len() != 0 { return Err(SnekError::SnekSyntaxError); }
    semantic_checker(&sexp)?;

    Ok(sexp)
}

fn semantic_checker_define<'a>(sexp_list: &[Sexp<'a>]) -> ParseResult<()> {
    // Semantics for define requires the sexp_list to have two elements.
    // If the define is a shorthand lambda, the first element is an expression
    // with at least one element, all being identifiers, the second being anything
    //
    // Otherwise it is a definition of an identifer, where the first item is an
    // atom and must be an identifier

    if sexp_list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    if !match &sexp_list[0] {
        Sexp::Expression(expression) 
            => expression.len() > 0 && expression.iter().all(|sexp| matches!(sexp, Sexp::Atom(Literal::Identifier(_)))),
        Sexp::Atom(atom) => matches!(atom, Literal::Identifier(_))
    } {
        return Err(SnekError::SnekSyntaxError)
    }

    semantic_checker(&sexp_list[1])
}

fn semantic_checker_lambda<'a>(sexp_list: &[Sexp<'a>]) -> ParseResult<()> {
    // Semantics for lambda expressions requires the sexp list to have two
    // elements. The first must be an expression containing all atoms of type
    // identifier literals, and the second can be anything

    if sexp_list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    if !match &sexp_list[0] {
        Sexp::Expression(expression) => expression.iter().all(|sexp| matches!(sexp, Sexp::Atom(Literal::Identifier(_)))),
        Sexp::Atom(_) => false
    } {
        return Err(SnekError::SnekSyntaxError);
    }

    semantic_checker(&sexp_list[1])
}

fn semantic_checker<'a>(sexp: &Sexp<'a>) -> ParseResult<()> {
    match sexp {
        Sexp::Expression(expression) if expression.get(0) == Some(&Sexp::Atom(Literal::Identifier("define")))
            => semantic_checker_define(&expression[1..]),
        Sexp::Expression(expression) if expression.get(0) == Some(&Sexp::Atom(Literal::Identifier("lambda")))
            => semantic_checker_lambda(&expression[1..]),
        _ => Ok(())
    }
}

#[cfg(test)]
mod tests {
    use anyhow::bail;

    use crate::test_utils::{all_testcases, load_test_pair, TestOutput};

    use super::*;

    fn assert_can_parse(testcase: (usize, usize), input: String, expected_result: Result<TestOutput, SnekError>) -> anyhow::Result<()> {
        let parse_result = parser(&input);
        match (parse_result, expected_result) {
            (Ok(result), Err(expected @ SnekError::SnekSyntaxError)) => bail!("Testcase {}:{} - Expected {:?} but got {:?}", testcase.0, testcase.1, expected, result), 
            (Err(result), Ok(expected)) => bail!("Testcase {}:{} - Expected {:?} but got {:?}", testcase.0, testcase.1, expected, result), 
            (Err(result), Err(expected @ SnekError::SnekSyntaxError)) if result != expected 
                => bail!("Testcase {}:{} - Expected {:?} but got {:?}", testcase.0, testcase.1, expected, result),
            _ => Ok(())
        }
    }

    #[test]
    fn parse_testcases() -> anyhow::Result<()> {
        for testcase in all_testcases() {
            println!("Running testcase {}", testcase);
            let entries = load_test_pair(testcase)?;

            for (lineno, (input, expected)) in entries.into_iter().enumerate() {
                assert_can_parse((testcase, lineno), input, expected.into())?;
            }
        }

        Ok(())
    }
}
