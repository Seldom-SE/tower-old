use std::{env, fs::File, io::prelude::*, path::Path};

// // T
// // o
// // w v0.1.0 by Seldom 2020
// // e
// // r
//
// use std::{
//     fmt::{Display, Formatter, Result},
//     io::{stdin, stdout, Write},
// };
//
// #[derive(Clone, Default)]
// struct State {
//     a: Option<Value>,
//     b: Option<Value>,
//     c: Option<Value>,
// }
//
// impl State {
//     fn get_register(&self, register: &Register) -> Option<Value> {
//         match register {
//             Register::A => self.a.clone(),
//             Register::B => self.b.clone(),
//             Register::C => self.c.clone(),
//         }
//     }
//
//     fn set_register(&mut self, register: &Register, value: Option<Value>) {
//         if let None = value {
//             return;
//         }
//         match register {
//             Register::A => self.a = value.clone(),
//             Register::B => self.b = value.clone(),
//             Register::C => self.c = value.clone(),
//         }
//     }
// }
//
// #[derive(Clone)]
// enum Register {
//     A,
//     B,
//     C,
// }
//
// impl Register {
//     fn from_char(character: char) -> Self {
//         match character {
//             'a' => Self::A,
//             'b' => Self::B,
//             'c' => Self::C,
//             x => panic!(format!(
//                 "Register::from_char: Attempted to parse Register from char: {}",
//                 x
//             )),
//         }
//     }
// }
//
// enum Instruction {
//     Assign(Register, Expression),
//     Jump(usize),
//     Write(Expression),
//     Condition(Expression, Box<Instruction>),
//     Extract(Expression),
// }
//
// impl Instruction {
//     fn parse(program: &Vec<char>, pointer: usize) -> (Self, usize) {
//         match program[pointer] {
//             'a' | 'b' | 'c' => {
//                 let (expression, new_pointer) = Expression::parse(program, pointer + 1);
//                 (
//                     Self::Assign(Register::from_char(program[pointer]), expression),
//                     new_pointer,
//                 )
//             }
//             '[' => {
//                 let mut char_pointer = pointer + 1;
//                 let mut groups = 1;
//                 while groups > 0 {
//                     char_pointer += 1;
//                     if program[char_pointer] == ']' {
//                         groups -= 1;
//                     } else if program[char_pointer] == '[' {
//                         groups += 1;
//                     }
//                 }
//                 (Self::Jump(pointer + 1), char_pointer + 1)
//             }
//             ']' => {
//                 let mut char_pointer = pointer - 1;
//                 let mut groups = 1;
//                 while groups > 0 {
//                     char_pointer -= 1;
//                     if program[char_pointer] == ']' {
//                         groups += 1;
//                     } else if program[char_pointer] == '[' {
//                         groups -= 1;
//                     }
//                 }
//                 (Self::Jump(char_pointer + 1), pointer + 1)
//             }
//             'W' => {
//                 let (expression, pointer) = Expression::parse(program, pointer + 1);
//                 (Self::Write(expression), pointer)
//             }
//             '?' => {
//                 let (expression, pointer) = Expression::parse(program, pointer + 1);
//                 let (instruction, pointer) = Self::parse(program, pointer);
//                 (Self::Condition(expression, Box::new(instruction)), pointer)
//             }
//             'X' => {
//                 let (expression, pointer) = Expression::parse(program, pointer + 1);
//                 (Self::Extract(expression), pointer)
//             }
//             x => panic!(format!("Unexpected instruction at {}: {}", pointer, x)),
//         }
//     }
//
//     fn execute(self, mut state: State) -> (State, Option<usize>) {
//         let mut destination = None;
//         match self {
//             Self::Assign(register, expression) => {
//                 state.set_register(&register, expression.evaluate(&state))
//             }
//             Self::Jump(dest) => destination = Some(dest),
//             Self::Write(expression) => {
//                 if let Some(value) = expression.evaluate(&state) {
//                     print!("{}", value);
//                     stdout().flush().expect("Failed to flush stdout");
//                 }
//             }
//             Self::Condition(expression, instruction) => {
//                 let (new_state, new_destination) = match expression.evaluate(&state) {
//                     Some(Value::Boolean(true))
//                     | Some(Value::Character(_))
//                     | Some(Value::State(_)) => instruction.execute(state),
//                     Some(Value::Boolean(false)) | Some(Value::Integer(0)) | None => {
//                         (state, destination)
//                     }
//                     Some(Value::Integer(_)) => instruction.execute(state),
//                 };
//                 state = new_state;
//                 destination = new_destination;
//             }
//             Self::Extract(expression) => match expression.evaluate(&state) {
//                 Some(Value::State(extracted_state)) => {
//                     for register in &[Register::A, Register::B, Register::C] {
//                         if let Some(value) = extracted_state.get_register(register) {
//                             state.set_register(register, Some(value));
//                         }
//                     }
//                 }
//                 _ => (),
//             },
//         }
//         (state, destination)
//     }
// }
//
// enum Expression {
//     Literal(Value),
//     Register(Register),
//     Sum(Box<Expression>, Box<Expression>),
//     Difference(Box<Expression>, Box<Expression>),
//     Product(Box<Expression>, Box<Expression>),
//     Quotient(Box<Expression>, Box<Expression>),
//     Modulus(Box<Expression>, Box<Expression>),
//     Equals(Box<Expression>, Box<Expression>),
//     GreaterThan(Box<Expression>, Box<Expression>),
//     LessThan(Box<Expression>, Box<Expression>),
//     Read,
//     ReadString(Register, Register),
//     Archive(Vec<Register>),
// }
//
// impl Expression {
//     fn parse(program: &Vec<char>, mut pointer: usize) -> (Self, usize) {
//         match program[pointer] {
//             '0'..='9' => {
//                 let start = pointer;
//                 let end = loop {
//                     pointer += 1;
//                     if let '0'..='9' = program[pointer] {
//                     } else {
//                         break pointer;
//                     }
//                 };
//                 (
//                     Self::Literal(Value::Integer(
//                         program[start..end]
//                             .iter()
//                             .map(|c| c.to_digit(10).unwrap())
//                             .sum::<u32>() as i32,
//                     )),
//                     end,
//                 )
//             }
//             '\'' => match program[pointer + 1] {
//                 '\\' => match program[pointer + 2] {
//                     'n' => (Self::Literal(Value::Character('\n')), pointer + 3),
//                     x => panic!(format!("Unexpected escape sequence at {}: {}", pointer, x)),
//                 },
//                 x => (Self::Literal(Value::Character(x)), pointer + 2),
//             },
//             '"' => {
//                 let beginning = pointer;
//                 let end = loop {
//                     pointer += 1;
//                     if program[pointer] == '\\' {
//                         pointer += 1;
//                     } else if program[pointer] == '"' {
//                         break pointer;
//                     }
//                 };
//                 let stack_register = Register::from_char(program[end + 1]);
//                 let value_register = Register::from_char(program[end + 2]);
//                 (
//                     Expression::Literal(Value::from_string(
//                         program,
//                         beginning + 1,
//                         end,
//                         &stack_register,
//                         &value_register,
//                     )),
//                     end + 3,
//                 )
//             }
//             'a' | 'b' | 'c' => (
//                 Self::Register(Register::from_char(program[pointer])),
//                 pointer + 1,
//             ),
//             '+' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::Sum(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '-' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::Difference(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '*' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::Product(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '/' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::Quotient(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '%' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::Modulus(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '=' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::Equals(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '>' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::GreaterThan(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             '<' => {
//                 let (expression_1, pointer) = Self::parse(program, pointer + 1);
//                 let (expression_2, pointer) = Self::parse(program, pointer);
//                 (
//                     Self::LessThan(Box::new(expression_1), Box::new(expression_2)),
//                     pointer,
//                 )
//             }
//             'R' => (Self::Read, pointer + 1),
//             'S' => (
//                 Self::ReadString(
//                     Register::from_char(program[pointer + 1]),
//                     Register::from_char(program[pointer + 2]),
//                 ),
//                 pointer + 3,
//             ),
//             '[' => {
//                 let mut registers = Vec::new();
//                 loop {
//                     pointer += 1;
//                     if program[pointer] == ']' {
//                         break;
//                     }
//                     registers.push(Register::from_char(program[pointer]));
//                 }
//                 (Self::Archive(registers), pointer + 1)
//             }
//             x => panic!(format!("Unexpected expression at {}: {}", pointer, x)),
//         }
//     }
//
//     fn evaluate(self, state: &State) -> Option<Value> {
//         match self {
//             Self::Literal(value) => Some(value),
//             Self::Register(register) => state.get_register(&register),
//             Self::Sum(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Integer(integer_1 + integer_2))
//                     }
//                     (Some(Value::Character(character)), Some(Value::Integer(integer))) => {
//                         Some(Value::Character((character as i32 + integer) as u8 as char))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::Difference(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Integer(integer_1 - integer_2))
//                     }
//                     (Some(Value::Character(character)), Some(Value::Integer(integer))) => {
//                         Some(Value::Character((character as i32 - integer) as u8 as char))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::Product(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Integer(integer_1 * integer_2))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::Quotient(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Integer(integer_1 / integer_2))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::Modulus(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Integer(integer_1 % integer_2))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::Equals(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Boolean(boolean_1)), Some(Value::Boolean(boolean_2))) => {
//                         Some(Value::Boolean(boolean_1 == boolean_2))
//                     }
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Boolean(integer_1 == integer_2))
//                     }
//                     (Some(Value::Character(character_1)), Some(Value::Character(character_2))) => {
//                         Some(Value::Boolean(character_1 == character_2))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::GreaterThan(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Boolean(integer_1 > integer_2))
//                     }
//                     (Some(Value::Character(character_1)), Some(Value::Character(character_2))) => {
//                         Some(Value::Boolean(character_1 > character_2))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::LessThan(expression_1, expression_2) => {
//                 match (expression_1.evaluate(state), expression_2.evaluate(state)) {
//                     (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) => {
//                         Some(Value::Boolean(integer_1 < integer_2))
//                     }
//                     (Some(Value::Character(character_1)), Some(Value::Character(character_2))) => {
//                         Some(Value::Boolean(character_1 < character_2))
//                     }
//                     _ => None,
//                 }
//             }
//             Self::Read => Some(Value::Integer(get_input().trim().parse().unwrap())),
//             Self::ReadString(stack_register, value_register) => {
//                 let string = get_input();
//                 Some(Value::from_string(
//                     &string.chars().collect(),
//                     0,
//                     string.len() - 1,
//                     &stack_register,
//                     &value_register,
//                 ))
//             }
//             Self::Archive(registers) => {
//                 let mut archive = State::default();
//                 for register in registers {
//                     archive.set_register(&register, state.get_register(&register));
//                 }
//                 Some(Value::State(Box::new(archive)))
//             }
//         }
//     }
// }
//
// #[derive(Clone)]
// enum Value {
//     Boolean(bool),
//     Integer(i32),
//     Character(char),
//     State(Box<State>),
// }
//
// impl Value {
//     fn to_string(&self) -> String {
//         match self {
//             Self::Boolean(_) => "".to_string(),
//             Self::Integer(integer) => integer.to_string(),
//             Self::Character(character) => character.to_string(),
//             Self::State(state) => {
//                 let mut string_1 = String::new();
//                 let mut string_2 = String::new();
//                 for value in [&state.a, &state.b, &state.c].iter() {
//                     match value {
//                         Some(val) => {
//                             if let Self::State(_) = val {
//                                 string_2 += &val.to_string();
//                             } else {
//                                 string_1 += &val.to_string();
//                             }
//                         }
//                         None => (),
//                     }
//                 }
//                 string_1 + &string_2
//             }
//         }
//     }
//
//     fn from_string(
//         string: &Vec<char>,
//         beginning: usize,
//         end: usize,
//         stack_register: &Register,
//         value_register: &Register,
//     ) -> Self {
//         let mut pointer = end;
//         let mut value = Value::Boolean(false);
//         loop {
//             if pointer == beginning {
//                 break value;
//             }
//             pointer -= 1;
//             let escaped = pointer > beginning && string[pointer - 1] == '\\';
//             let mut state = State::default();
//             state.set_register(stack_register, Some(value));
//             state.set_register(
//                 value_register,
//                 Some(Value::Character(if escaped {
//                     let character = match string[pointer] {
//                         'n' => '\n',
//                         '"' => '"',
//                         _ => panic!(format!(
//                             "Unexpected escape sequence in string: {}",
//                             string[pointer]
//                         )),
//                     };
//                     pointer -= 1;
//                     character
//                 } else {
//                     string[pointer]
//                 })),
//             );
//             value = Value::State(Box::new(state));
//         }
//     }
// }
//
// impl Display for Value {
//     fn fmt(&self, f: &mut Formatter<'_>) -> Result {
//         write!(f, "{}", self.to_string())
//     }
// }
//
// // Examples:
//
// // From Exercises for Programmers by Brian P. Hogan
//
// // W"What is your name? "abaSabW"Hello, "abWaW", nice to meet you!\n"ab
// // W"What is the input string? "abaSacW"\""abb[a]c0?a[c+c1b[bc]XaXb?a]WbW"\" has "abWcW" characters.\n"ab
// // W"What is the input string? "ab
// // aSac
// // W"\""ab
// // b[a]
// // c0
// // ?a[
// //   c+c1
// //   b[bc]
// //   Xa
// //   Xb
// // ?a]
// // Wb
// // W"\" has "abWcW" characters.\n"ab
// // W"What is the quote? "abaSabW"Who said it? "abbSbaWbW" says, \""abWaW"\"\n"ab
// // W"Enter a noun: "abaSacW"Enter a verb: "abbSbcW"Enter an adjective: "abcScaa[ac]W"Enter an adverb: "abcScaW"Do you "abWbW" your "abbcXaWcW" "abWaW" "abWbW"? That's hilarious!\n"ab
// // W"What is the first number? "abaRW"What is the second number? "abbRWaW" + "abWbW" = "abW+abW'\nWaW" - "abWbW" = "abW-abW'\nWaW" * "abWbW" = "abW*abW'\nWaW" / "abWbW" = "abW/abW'\n
//
// // From Code Golf Stack Exchange:
//
// // Factorial:
// // aRb1?>a0[b*aba-a1?>a0]Wb
//
// // Hello, World!:
// // W"Hello, World!"ab
//
// fn main() {
//     execute(r#"W"What is the input string? "abaSacW"\""abb[a]c0?a[c+c1b[bc]XaXb?a]WbW"\" has "abWcW" characters.\n"ab"#.chars().collect());
// }
//
// fn execute(program: Vec<char>) {
//     let mut pointer = 0;
//     let mut state = State::default();
//     while pointer < program.len() {
//         let (instruction, new_pointer) = Instruction::parse(&program, pointer);
//         let (new_state, dest) = instruction.execute(state);
//         state = new_state;
//         if let Some(destination) = dest {
//             pointer = destination;
//         } else {
//             pointer = new_pointer;
//         }
//     }
// }
//
// fn get_input() -> String {
//     let mut string = String::new();
//     stdin().read_line(&mut string).expect("Failed to read line");
//     string
// }

// Language spec:
//
// Statements:  ,.[]#abc?!
// Expressions: ,._+-*/%[]=<>&|^!abc?
//
// , - Read / Write as character
// . - Read / Write as number
// _ - Check whether the buffer contains a value
// + - Add
// - - Subtract
// * - Multiply
// / - Divide
// % - Modulus
// a - Get/Set a
// b - Get/Set b
// c - Get/Set c
// ' - Number literal
// " - Character literal
// [ - Loop / Compress start
// ] - Loop / Compress end
// # - Extract
// = - Equals
// > - Greater Than
// < - Less Than
// & - And
// | - Or
// ^ - Xor
// ? - Conditional expression / If
// ! - Not / If not
// ~ - Negative
//
// \a - Alarm
// \b - Backspace
// \f - Form feed
// \n - New line
// \r - Carriage return
// \t - Tab
// \v - Vertical tab
// \\ - Backslash

#[derive(Debug)]
enum Value {
    Bool(bool),
    Int(i64),
    Float(f64),
    Char(char),
}

#[derive(Debug)]
enum Token {
    Literal(Value),
    Negative,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulus,
    Equals,
    GreaterThan,
    LessThan,
    And,
    Or,
    Xor,
    A,
    B,
    C,
    Period,
    Comma,
    Underscore,
    Question,
    Exclamation,
    LeftBracket,
    RightBracket,
    Hash,
}

#[derive(Clone)]
enum TokenParseState {
    Token,
    NumLiteral(usize, String),
    NumLiteralPeriod(usize, String, usize),
    CharLiteral,
}

#[derive(Debug)]
struct TokenList(Vec<(Token, usize)>);

impl TokenList {
    fn from_string(string: String) -> Self {
        let mut tokens = Vec::new();
        let mut state = TokenParseState::Token;
        for (i, character) in string.chars().enumerate() {
            // If we're in a num literal, and the current character definitely ends the literal
            // (anything but 0-9, plus . if the last character was not a .),
            // then we should handle resolving the literal here, and change the state accordingly
            // to prepare for matching this character
            if let TokenParseState::NumLiteral(literal_i, num_literal)
            | TokenParseState::NumLiteralPeriod(literal_i, num_literal, _) = &state
            {
                if let '0'..='9' = character {
                } else {
                    if let (TokenParseState::NumLiteral(_, _), '.') = (&state, &character) {
                    } else {
                        tokens.push((
                            Token::Literal(match num_literal.parse() {
                                Ok(int) => Value::Int(int),
                                Err(_) => match num_literal.parse() {
                                    Ok(float) => Value::Float(float),
                                    Err(_) => {
                                        panic!("Failed to parse num literal '{}' at {}, on token '{}' at {}", num_literal, literal_i, character, i)
                                    }
                                },
                            }),
                            *literal_i,
                        ));
                        if let TokenParseState::NumLiteralPeriod(_, _, period_i) = &state {
                            tokens.push((Token::Period, *period_i));
                        }
                        state = TokenParseState::Token;
                    }
                }
            }

            let (new_state, token) = match (state, character) {
                (state, '\t') | (state, '\n') | (state, '\x0c') | (state, '\r') | (state, ' ') => (state, None), // Ignore whitespace
                (TokenParseState::Token, '\'') => (TokenParseState::NumLiteral(i, String::new()), None),
                (TokenParseState::Token, '"') => (TokenParseState::CharLiteral, None),
                (TokenParseState::Token, '~') => (TokenParseState::Token, Some(Token::Negative)),
                (TokenParseState::Token, '+') => (TokenParseState::Token, Some(Token::Add)),
                (TokenParseState::Token, '-') => (TokenParseState::Token, Some(Token::Subtract)),
                (TokenParseState::Token, '*') => (TokenParseState::Token, Some(Token::Multiply)),
                (TokenParseState::Token, '/') => (TokenParseState::Token, Some(Token::Divide)),
                (TokenParseState::Token, '%') => (TokenParseState::Token, Some(Token::Modulus)),
                (TokenParseState::Token, '=') => (TokenParseState::Token, Some(Token::Equals)),
                (TokenParseState::Token, '>') => (TokenParseState::Token, Some(Token::GreaterThan)),
                (TokenParseState::Token, '<') => (TokenParseState::Token, Some(Token::LessThan)),
                (TokenParseState::Token, '&') => (TokenParseState::Token, Some(Token::And)),
                (TokenParseState::Token, '|') => (TokenParseState::Token, Some(Token::Or)),
                (TokenParseState::Token, '^') => (TokenParseState::Token, Some(Token::Xor)),
                (TokenParseState::Token, 'a') => (TokenParseState::Token, Some(Token::A)),
                (TokenParseState::Token, 'b') => (TokenParseState::Token, Some(Token::B)),
                (TokenParseState::Token, 'c') => (TokenParseState::Token, Some(Token::C)),
                (TokenParseState::Token, '.') => (TokenParseState::Token, Some(Token::Period)),
                (TokenParseState::Token, ',') => (TokenParseState::Token, Some(Token::Comma)),
                (TokenParseState::Token, '_') => (TokenParseState::Token, Some(Token::Underscore)),
                (TokenParseState::Token, '?') => (TokenParseState::Token, Some(Token::Question)),
                (TokenParseState::Token, '!') => (TokenParseState::Token, Some(Token::Exclamation)),
                (TokenParseState::Token, '[') => (TokenParseState::Token, Some(Token::LeftBracket)),
                (TokenParseState::Token, ']') => (TokenParseState::Token, Some(Token::RightBracket)),
                (TokenParseState::Token, '#') => (TokenParseState::Token, Some(Token::Hash)),
                (TokenParseState::Token, _) => panic!("Unknown token '{}' at {}", i, character),
                (TokenParseState::NumLiteral(literal_i, mut num_literal), '0'..='9') => {
                    num_literal.push(character);
                    (TokenParseState::NumLiteral(literal_i, num_literal), None)
                }
                (TokenParseState::NumLiteral(literal_i, num_literal), '.') =>
                    (TokenParseState::NumLiteralPeriod(literal_i, num_literal, i), None),
                (TokenParseState::NumLiteralPeriod(literal_i, mut num_literal, _), '0'..='9') => {
                    num_literal.push('.');
                    num_literal.push(character);
                    (TokenParseState::NumLiteral(literal_i, num_literal), None)
                },
                (TokenParseState::NumLiteral(literal_i, num_literal), _) | (TokenParseState::NumLiteralPeriod(literal_i, num_literal, _), _) => panic!("Num literal '{}' at {} wasn't already parsed when it should have, on token '{}', at {}", literal_i, num_literal, character, i),
                (TokenParseState::CharLiteral, _) => (TokenParseState::Token, Some(Token::Literal(Value::Char(character)))),
            };
            state = new_state;

            if let Some(token) = token {
                tokens.push((token, i));
            }
        }
        Self(tokens)
    }
}

#[derive(Debug)]
enum Register {
    A,
    B,
    C,
}

#[derive(Debug)]
enum Expression {
    Not(Box<Expression>),
    And(Box<Expression>, Box<Expression>),
    Register(Register),
}

impl Expression {
    fn from_token_list(token_list: &TokenList, start: usize) -> (Self, usize) {
        (Self::Register(Register::A), 0)
    }
}

// Statements:  ,.[]#abc?!
#[derive(Debug)]
enum Statement {
    Assign(Register, Expression),
    PrintNum(Expression),
    PrintChar(Expression),
    If(Expression, Box<Statement>),
    IfNot(Expression, Box<Statement>),
    Loop(Expression, Box<StatementList>, Expression),
    LoopEnd,
    Extract(Expression),
}

impl Statement {
    fn from_token_list(token_list: &TokenList, start: usize) -> (Self, usize) {
        let TokenList(tokens) = token_list;
        let (statement_token, i) = tokens.get(start).expect("Expected a statement at EOF");
        match statement_token {
            Token::A | Token::B | Token::C => {
                let (expression, pos) = Expression::from_token_list(token_list, start + 1);
                (
                    Self::Assign(
                        match statement_token {
                            Token::A => Register::A,
                            Token::B => Register::B,
                            Token::C => Register::C,
                            _ => panic!("Unreachable"),
                        },
                        expression,
                    ),
                    pos,
                )
            }
            Token::Period | Token::Comma => {
                let (expression, pos) = Expression::from_token_list(token_list, start + 1);
                (
                    match statement_token {
                        Token::Period => Self::PrintNum(expression),
                        Token::Comma => Self::PrintNum(expression),
                        _ => panic!("Unreachable"),
                    },
                    pos,
                )
            }
            Token::Question | Token::Exclamation => {
                let (expression, pos) = Expression::from_token_list(token_list, start + 1);
                let (statement, pos) = Statement::from_token_list(token_list, pos);
                if let Statement::Loop(enter_condition, statement_list, loop_condition) = statement
                {
                    (
                        Statement::Loop(
                            Expression::And(
                                match statement_token {
                                    Token::Question => Box::new(expression),
                                    Token::Exclamation => {
                                        Box::new(Expression::Not(Box::new(expression)))
                                    }
                                    _ => panic!("Unreachable"),
                                },
                                Box::new(enter_condition),
                            ),
                            statement_list,
                            loop_condition,
                        ),
                        pos,
                    )
                } else {
                    (
                        match statement_token {
                            Token::Question => Statement::If(expression, Box::new(statement)),
                            Token::Exclamation => Statement::IfNot(expression, Box::new(statement)),
                            _ => panic!("Unreachable"),
                        },
                        pos,
                    )
                }
            }
            Token::LeftBracket => {
                let mut pos = start + 1;
                let mut level = 0;
                loop {
                    let (token, token_i) = tokens.get(pos).expect(&format!(
                        "Expected right bracket for left bracket at {} before EOF",
                        i
                    ));
                    match token {
                        Token::LeftBracket => level += 1,
                        Token::RightBracket => {
                            if level <= 0 {
                                break;
                            } else {
                                level -= 1
                            }
                        }
                        _ => {}
                    }
                }
                // Probably need a recursive Statement::If::as_expression and
                // Statement::IfNot::as_expression to resolve this cleanly
                let statement_list = StatementList::from_token_list(token_list, start + 1, pos - 1);
                let StatementList(statements) = statement_list;
                if let Some(last_statement) = statements.last() {
                    match last_statement {
                        Statement::If(_, if_statement) | Statement::IfNot(_, if_statement) => 
                    }
                }
            }
        }
        //        match statement_token {
        //            Token::A =>
        //
        //    // Literal(Value),
        //    // Negative,
        //    // Add,
        //    // Subtract,
        //    // Multiply,
        //    // Divide,
        //    // Modulus,
        //    // Equals,
        //    // GreaterThan,
        //    // LessThan,
        //    // And,
        //    // Or,
        //    // Xor,
        //    // A,
        //    // B,
        //    // C,
        //    // Period,
        //    // Comma,
        //    // Underscore,
        //    // Question,
        //    // Exclamation,
        //    // LeftBracket,
        //    // RightBracket,
        //    // Hash,
        //        }
    }
}

#[derive(Debug)]
struct StatementList(Vec<Statement>);

impl StatementList {
    fn from_token_list(token_list: &TokenList, start: usize, end: usize) -> Self {
        let mut statements = Vec::new();
        let mut pos = start;
        while pos < end {
            let (statement, new_pos) = Statement::from_token_list(token_list, pos);
            statements.push(statement);
            pos = new_pos;
        }
        Self(statements)
    }
}

#[derive(Debug)]
struct Program(StatementList);

impl Program {
    fn from_token_list(token_list: TokenList) -> Self {
        let TokenList(tokens) = &token_list;
        Self(StatementList::from_token_list(&token_list, 0, tokens.len()))
    }
}

fn main() {
    let mut program = String::new();
    File::open(&Path::new(
        env::args()
            .collect::<Vec<String>>()
            .get(1)
            .expect("Missing file argument"),
    ))
    .expect("Failed to open file")
    .read_to_string(&mut program)
    .expect("Failed to read file");

    println!(
        "{:?}",
        Program::from_token_list(TokenList::from_string(program))
    );
}
