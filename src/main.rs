// T
// o
// w v0.2.0 by Seldom 2020
// e
// r

use std::{
    collections::VecDeque,
    fmt::{Display, Formatter, Result},
    io::{stdin, stdout, Write},
};

#[derive(Clone, Default)]
struct State {
    a: Option<Value>,
    b: Option<Value>,
    c: Option<Value>,
}

impl State {
    fn get_register(&self, register: &Register) -> Option<Value> {
        match register {
            Register::A => self.a.clone(),
            Register::B => self.b.clone(),
            Register::C => self.c.clone(),
        }
    }

    fn set_register(&mut self, register: &Register, value: Option<Value>) {
        if let None = value {
            return;
        }
        match register {
            Register::A => self.a = value.clone(),
            Register::B => self.b = value.clone(),
            Register::C => self.c = value.clone(),
        }
    }
}

#[derive(Clone)]
enum Register {
    A,
    B,
    C,
}

impl Register {
    fn from_char(character: char) -> Self {
        match character {
            'a' => Self::A,
            'b' => Self::B,
            'c' => Self::C,
            x => panic!(format!("Register::from_char: Attempted to parse Register from char: {}", x)),
        }
    }
}

enum Instruction {
    Assign(Register, Expression),
    Jump(usize),
    Write(Expression),
    Condition(Expression, Box<Instruction>),
    Extract(Expression),
}

impl Instruction {
    fn parse(program: &Vec<char>, pointer: usize) -> (Self, usize) {
        match program[pointer] {
            'a' | 'b' | 'c' => {
                let (expression, new_pointer) = Expression::parse(program, pointer + 1);
                (Self::Assign(Register::from_char(program[pointer]), expression), new_pointer)
            },
            '[' => {
                let mut char_pointer = pointer + 1;
                let mut groups = 1;
                while groups > 0 {
                    char_pointer += 1;
                    if program[char_pointer] == ']' {
                        groups -= 1;
                    } else if program[char_pointer] == '[' {
                        groups += 1;
                    }
                }
                (Self::Jump(pointer + 1), char_pointer + 1)
            },
            ']' => {
                let mut char_pointer = pointer - 1;
                let mut groups = 1;
                while groups > 0 {
                    char_pointer -= 1;
                    if program[char_pointer] == ']' {
                        groups += 1;
                    } else if program[char_pointer] == '[' {
                        groups -= 1;
                    }
                }
                (Self::Jump(char_pointer + 1), pointer + 1)
            },
            '.' => {
                let (expression, pointer) = Expression::parse(program, pointer + 1);
                (Self::Write(expression), pointer)
            },
            '?' => {
                let (expression, pointer) = Expression::parse(program, pointer + 1);
                let (instruction, pointer) = Self::parse(program, pointer);
                (Self::Condition(expression, Box::new(instruction)), pointer)
            },
            'X' => {
                let (expression, pointer) = Expression::parse(program, pointer + 1);
                (Self::Extract(expression), pointer)
            },
            x => panic!(format!("Unexpected instruction at {}: {}", pointer, x)),
        }
    }

    fn execute(self, mut state: State, mut buffer: VecDeque<Option<char>>) -> (State, VecDeque<Option<char>>, Option<usize>) {
        let mut destination = None;
        match self {
            Self::Assign(register, expression) => state.set_register(&register, expression.evaluate(&state, &mut buffer)),
            Self::Jump(dest) => destination = Some(dest),
            Self::Write(expression) => {
                if let Some(value) = expression.evaluate(&state, &mut buffer) {
                    print!("{}", value);
                    stdout().flush().expect("Failed to flush stdout");
                }
            },
            Self::Condition(expression, instruction) => {
                let (new_state, new_buffer, new_destination) = match expression.evaluate(&state, &mut buffer) {
                    Some(Value::Boolean(true)) | Some(Value::Character(_)) | Some(Value::State(_)) => instruction.execute(state, buffer),
                    Some(Value::Boolean(false)) | Some(Value::Integer(0)) | None => (state, buffer, destination),
                    Some(Value::Integer(_)) => instruction.execute(state, buffer),
                };
                state = new_state;
                buffer = new_buffer;
                destination = new_destination;
            },
            Self::Extract(expression) => {
                match expression.evaluate(&state, &mut buffer) {
                    Some(Value::State(extracted_state)) => {
                        for register in &[Register::A, Register::B, Register::C] {
                            if let Some(value) = extracted_state.get_register(register) {
                                state.set_register(register, Some(value));
                            }
                        }
                    },
                    _ => (),
                }
            }
        }
        (state, buffer, destination)
    }
}

enum Expression {
    Literal(Value),
    Register(Register),
    Negation(Box<Expression>),
    Sum(Box<Expression>, Box<Expression>),
    Difference(Box<Expression>, Box<Expression>),
    Product(Box<Expression>, Box<Expression>),
    Quotient(Box<Expression>, Box<Expression>),
    Modulus(Box<Expression>, Box<Expression>),
    Equals(Box<Expression>, Box<Expression>),
    GreaterThan(Box<Expression>, Box<Expression>),
    LessThan(Box<Expression>, Box<Expression>),
    ReadCharacter,
    ReadInteger,
    Archive(Vec<Register>),
}

impl Expression {
    fn parse(program: &Vec<char>, mut pointer: usize) -> (Self, usize) {
        match program[pointer] {
            'T' => (Self::Literal(Value::Boolean(true)), pointer + 1),
            'F' => (Self::Literal(Value::Boolean(false)), pointer + 1),
            '0'..='9' => {
                let start = pointer;
                let end = loop {
                    pointer += 1;
                    if let '0'..='9' = program[pointer] {} else {
                        break pointer;
                    }
                };
                (Self::Literal(Value::Integer(program[start..end].iter().map(|c| c.to_digit(10).unwrap()).sum::<u32>() as i32)), end)
            },
            '"' => (Self::Literal(Value::Character(None)), pointer + 1),
            '\'' => {
                match program[pointer + 1] {
                    '\\' => match program[pointer + 2] {
                        'n' => (Self::Literal(Value::Character(Some('\n'))), pointer + 3),
                        x => panic!(format!("Unexpected escape sequence at {}: {}", pointer, x))
                    },
                    x => (Self::Literal(Value::Character(Some(x))), pointer + 2),
                }
            },
            'a' | 'b' | 'c' => (Self::Register(Register::from_char(program[pointer])), pointer + 1),
            '!' => {
                let (expression, pointer) = Self::parse(program, pointer + 1);
                (Self::Negation(Box::new(expression)), pointer)
            }
            '+' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::Sum(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '-' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::Difference(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '*' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::Product(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '/' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::Quotient(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '%' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::Modulus(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '=' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::Equals(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '>' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::GreaterThan(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            '<' => {
                let (expression_1, pointer) = Self::parse(program, pointer + 1);
                let (expression_2, pointer) = Self::parse(program, pointer);
                (Self::LessThan(Box::new(expression_1), Box::new(expression_2)), pointer)
            },
            ',' => (Self::ReadCharacter, pointer + 1),
            ';' => (Self::ReadInteger, pointer + 1),
            '[' => {
                let mut registers = Vec::new();
                loop {
                    pointer += 1;
                    if program[pointer] == ']' {
                        break;
                    }
                    registers.push(Register::from_char(program[pointer]));
                }
                (Self::Archive(registers), pointer + 1)
            },
            x => panic!(format!("Unexpected expression at {}: {}", pointer, x)),
        }
    }

    fn evaluate(self, state: &State, buffer: &mut VecDeque<Option<char>>) -> Option<Value> {
        match self {
            Self::Literal(value) => Some(value),
            Self::Register(register) => state.get_register(&register),
            Self::Negation(expression) => {
                match expression.evaluate(state, buffer) {
                    Some(Value::Boolean(boolean)) =>
                        Some(Value::Boolean(!boolean)),
                    _ => None,
                }
            },
            Self::Sum(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Integer(integer_1 + integer_2)),
                    (Some(Value::Character(Some(character))), Some(Value::Integer(integer))) =>
                        Some(Value::Character(Some((character as i32 + integer) as u8 as char))),
                    _ => None,
                }
            },
            Self::Difference(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Integer(integer_1 - integer_2)),
                    (Some(Value::Character(Some(character))), Some(Value::Integer(integer))) =>
                        Some(Value::Character(Some((character as i32 - integer) as u8 as char))),
                    _ => None,
                }
            },
            Self::Product(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Integer(integer_1 * integer_2)),
                    _ => None,
                }
            },
            Self::Quotient(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Integer(integer_1 / integer_2)),
                    _ => None,
                }
            },
            Self::Modulus(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Integer(integer_1 % integer_2)),
                    _ => None,
                }
            },
            Self::Equals(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Boolean(boolean_1)), Some(Value::Boolean(boolean_2))) =>
                        Some(Value::Boolean(boolean_1 == boolean_2)),
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Boolean(integer_1 == integer_2)),
                    (Some(Value::Character(character_1)), Some(Value::Character(character_2))) =>
                        Some(Value::Boolean(character_1 == character_2)),
                    _ => None,
                }
            },
            Self::GreaterThan(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Boolean(integer_1 > integer_2)),
                    (Some(Value::Character(character_1)), Some(Value::Character(character_2))) =>
                        Some(Value::Boolean(character_1 > character_2)),
                    _ => None,
                }
            },
            Self::LessThan(expression_1, expression_2) => {
                match (expression_1.evaluate(state, buffer), expression_2.evaluate(state, buffer)) {
                    (Some(Value::Integer(integer_1)), Some(Value::Integer(integer_2))) =>
                        Some(Value::Boolean(integer_1 < integer_2)),
                    (Some(Value::Character(character_1)), Some(Value::Character(character_2))) =>
                        Some(Value::Boolean(character_1 < character_2)),
                    _ => None,
                }
            },
            Self::ReadCharacter => {
                Some(Value::Character(match buffer.pop_back() {
                    Some(character) => character,
                    None => {
                        for character in get_input().chars() {
                            buffer.push_front(Some(character));
                        }
                        buffer.push_front(None);
                        buffer.pop_back().unwrap()
                    }
                }))
            },
            Self::ReadInteger => {
                Some(match get_input().trim().parse() {
                    Ok(integer) => Value::Integer(integer),
                    Err(_) => Value::Character(None)
                })
            },
            Self::Archive(registers) => {
                let mut archive = State::default();
                for register in registers {
                    archive.set_register(&register, state.get_register(&register));
                }
                Some(Value::State(Box::new(archive)))
            },
        }
    }
}

#[derive(Clone)]
enum Value {
    Boolean(bool),
    Integer(i32),
    Character(Option<char>),
    State(Box<State>),
}

impl Value {
    fn to_string(&self) -> String {
        match self {
            Self::Boolean(_) => "".to_string(),
            Self::Integer(integer) => integer.to_string(),
            Self::Character(Some(character)) => character.to_string(),
            Self::Character(None) => "".to_string(),
            Self::State(_) => "".to_string()
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.to_string())
    }
}

// Examples:

// Factorial:
// a;b1?>a0[b*aba-a1?>a0].b

// Scream very loudly:
// [.'A]

// Hello interpreter:
// [a,b=a'h?b[.'H.'e.'l.'l.'o.' .'W.'o.'r.'l.'d?F]?b]?!=a"[.'e.'r.'r?F]

// Running second maximum:
// b;cba,[a;?>ab[ba?>bc[bcca?F]?F].b?!=,"]

// Pascal's Triangle Generator
/*
c.
b4
a[b]
b3
[
    c-c1
    a[abc]
?c]
[
    Xa
    ?=b3[
        cb
        [
            c[bc]
            b2
            a[abc]
            Xc
            c-c1
        ?c]
    ]
    ?=b2[
        b1
    ]
    ?=b1[
        Xc
        ?|=c0=bc[
            b0
            c1
        ]
        !|=c0=bc[
            b-b1
            c[bc]
            
        ]
    ]
    ?b0[

    ]
?=b4]
*/

fn main() {
    execute(r#"b;cba;[?>ab[ba?>bc[bcca?F]?F].ba;?!=a"]"#.chars().collect());
}

fn execute(program: Vec<char>) {
    let mut pointer = 0;
    let mut state = State::default();
    let mut buffer = VecDeque::new();
    while pointer < program.len() {
        let (instruction, new_pointer) = Instruction::parse(&program, pointer);
        let (new_state, new_buffer, dest) = instruction.execute(state, buffer);
        state = new_state;
        buffer = new_buffer;
        if let Some(destination) = dest {
            pointer = destination;
        } else {
            pointer = new_pointer;
        }
    }
}

fn get_input() -> String {
    let mut string = String::new();
    stdin().read_line(&mut string).expect("Failed to read line");
    string.trim().to_string()
}