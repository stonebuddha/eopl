use std::rc::Rc;
use std::cell::RefCell;
use std::ops::Deref;
use std::fmt;

#[derive(Clone)]
pub enum Expr {
    Const(i64),
    Diff(Rc<Expr>, Rc<Expr>),
    IsZero(Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Var(u32),
    Let(Rc<Expr>, Rc<Expr>),
    Proc(Rc<Expr>),
    Call(Rc<Expr>, Rc<Expr>),
    Letrec(Rc<Expr>, Rc<Expr>),
}

type Env<T> = Option<Rc<Node<T>>>;

struct Node<T> {
    elem: T,
    next: Env<T>,
}

fn empty_env<T>() -> Env<T> {
    None
}

fn extend_env<T>(elem: T, next: Env<T>) -> Env<T> {
    Some(Rc::new(Node {
        elem: elem,
        next: next,
    }))
}

fn apply_env<T: Clone>(env: Env<T>, var: u32) -> T {
    let mut cur_env = env;
    let mut cur_var = var;
    while cur_var > 0 {
        let ref saved_env = cur_env.unwrap().next;
        cur_env = saved_env.clone();
        cur_var -= 1;
    };
    cur_env.unwrap().elem.clone()
}

#[derive(Clone)]
enum Value {
    NumVal(i64),
    BoolVal(bool),
    ProcVal(Rc<Expr>, Rc<RefCell<Env<Value>>>),
}

enum Continuation {
    EndCont,
    Diff1Cont(Rc<Expr>, Env<Value>, Box<Continuation>),
    Diff2Cont(Value, Box<Continuation>),
    IsZeroCont(Box<Continuation>),
    IfCont(Rc<Expr>, Rc<Expr>, Env<Value>, Box<Continuation>),
    LetCont(Rc<Expr>, Env<Value>, Box<Continuation>),
    Call1Cont(Rc<Expr>, Env<Value>, Box<Continuation>),
    Call2Cont(Value, Box<Continuation>),
}

enum Bounce {
    Ans(Option<Value>),
    Jump(Continuation, Value),
}

fn apply_cont(cont: Continuation, val: Value) -> Bounce {
    match cont {
        Continuation::EndCont => Bounce::Ans(Some(val)),
        Continuation::Diff1Cont(exp2, env, saved_cont) => {
            let val1 = val;
            value_of(&exp2, env, Box::new(Continuation::Diff2Cont(val1, saved_cont)))
        },
        Continuation::Diff2Cont(val1, saved_cont) => {
            let val2 = val;
            match (val1, val2) {
                (Value::NumVal(n1), Value::NumVal(n2)) => Bounce::Jump(*saved_cont, Value::NumVal(n1 - n2)),
                _ => Bounce::Ans(None),
            }
        },
        Continuation::IsZeroCont(saved_cont) => {
            let val1 = val;
            match val1 {
                Value::NumVal(n1) => Bounce::Jump(*saved_cont, Value::BoolVal(n1 == 0)),
                _ => Bounce::Ans(None),
            }
        },
        Continuation::IfCont(exp2, exp3, env, saved_cont) => {
            let val1 = val;
            match val1 {
                Value::BoolVal(true) => value_of(&exp2, env, saved_cont),
                Value::BoolVal(false) => value_of(&exp3, env, saved_cont),
                _ => Bounce::Ans(None),
            }
        },
        Continuation::LetCont(body, env, saved_cont) => {
            let val1 = val;
            value_of(&body, extend_env(val1, env), saved_cont)
        },
        Continuation::Call1Cont(rand, env, saved_cont) => {
            let rator_val = val;
            value_of(&rand, env, Box::new(Continuation::Call2Cont(rator_val, saved_cont)))
        },
        Continuation::Call2Cont(rator_val, saved_cont) => {
            let rand_val = val;
            match rator_val {
                Value::ProcVal(body, saved_env) => value_of(&body, extend_env(rand_val, saved_env.borrow().deref().clone()), saved_cont),
                _ => Bounce::Ans(None),
            }
        },
    }
}

fn value_of(exp: &Rc<Expr>, env: Env<Value>, cont: Box<Continuation>) -> Bounce {
    match *exp.as_ref() {
        Expr::Const(n) => Bounce::Jump(*cont, Value::NumVal(n)),
        Expr::Diff(ref exp1, ref exp2) => {
            value_of(exp1, env.clone(), Box::new(Continuation::Diff1Cont(exp2.clone(), env, cont)))
        },
        Expr::IsZero(ref exp1) => {
            value_of(exp1, env, Box::new(Continuation::IsZeroCont(cont)))
        },
        Expr::If(ref exp1, ref exp2, ref exp3) => {
            value_of(exp1, env.clone(), Box::new(Continuation::IfCont(exp2.clone(), exp3.clone(), env, cont)))
        },
        Expr::Var(var) => Bounce::Jump(*cont, apply_env(env, var)),
        Expr::Let(ref exp1, ref body) => {
            value_of(exp1, env.clone(), Box::new(Continuation::LetCont(body.clone(), env, cont)))
        },
        Expr::Proc(ref body) => Bounce::Jump(*cont, Value::ProcVal(body.clone(), Rc::new(RefCell::new(env)))),
        Expr::Call(ref rator, ref rand) => {
            value_of(rator, env.clone(), Box::new(Continuation::Call1Cont(rand.clone(), env, cont)))
        },
        Expr::Letrec(ref p_body, ref letrec_body) => {
            let saved_env = Rc::new(RefCell::new(None));
            let p_val = Value::ProcVal(p_body.clone(), saved_env.clone());
            let new_env = extend_env(p_val, env);
            *saved_env.borrow_mut() = new_env.clone();
            value_of(letrec_body, new_env, cont)
        },
    }
}

pub enum ExtValue {
    NumVal(i64),
    BoolVal(bool),
    ProcVal,
}

impl fmt::Display for ExtValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExtValue::NumVal(n) => write!(f, "{}", n),
            ExtValue::BoolVal(b) => write!(f, "#{}", if b { "true" } else { "false" }),
            ExtValue::ProcVal => write!(f, "<proc>"),
        }
    }
}

impl Expr {
    pub fn eval(&self) -> Option<ExtValue> {
        let mut bounce = value_of(&Rc::new(self.clone()), empty_env(), Box::new(Continuation::EndCont));
        let result;
        loop {
            match bounce {
                Bounce::Ans(answer) => {
                    result = answer;
                    break;
                },
                Bounce::Jump(cont, val) => {
                    bounce = apply_cont(cont, val);
                }
            }
        };
        result.map(|val| {
            match val {
                Value::NumVal(n) => ExtValue::NumVal(n),
                Value::BoolVal(b) => ExtValue::BoolVal(b),
                Value::ProcVal(_, _) => ExtValue::ProcVal,
            }
        })
    }
}
