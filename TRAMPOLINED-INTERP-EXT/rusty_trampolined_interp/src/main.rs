mod core;

use std::rc::Rc;
use core::Expr::*;

fn main() {
    let exp = If(Rc::new(IsZero(Rc::new(Const(0)))), Rc::new(Const(42)), Rc::new(Const(35)));
    exp.eval().map(|val| println!("{}", val));
    let exp = Let(Rc::new(Const(35)), Rc::new(Let(Rc::new(Const(42)), Rc::new(Var(0)))));
    exp.eval().map(|val| println!("{}", val));
    let exp = Call(Rc::new(Proc(Rc::new(Diff(Rc::new(Var(0)), Rc::new(Const(-1)))))), Rc::new(Const(3)));
    exp.eval().map(|val| println!("{}", val));
    let exp = Letrec(Rc::new(If(Rc::new(IsZero(Rc::new(Var(0)))), Rc::new(Const(0)), Rc::new(Diff(Rc::new(Var(0)), Rc::new(Diff(Rc::new(Const(0)), Rc::new(Call(Rc::new(Var(1)), Rc::new(Diff(Rc::new(Var(0)), Rc::new(Const(1)))))))))))), Rc::new(Call(Rc::new(Var(0)), Rc::new(Const(1000000)))));
    exp.eval().map(|val| println!("{}", val));
    let exp = Letrec(Rc::new(Proc(Rc::new(If(Rc::new(IsZero(Rc::new(Var(1)))), Rc::new(Var(0)), Rc::new(Call(Rc::new(Call(Rc::new(Var(2)), Rc::new(Diff(Rc::new(Var(1)), Rc::new(Const(1)))))), Rc::new(Diff(Rc::new(Var(0)), Rc::new(Diff(Rc::new(Const(0)), Rc::new(Var(1)))))))))))), Rc::new(Call(Rc::new(Call(Rc::new(Var(0)), Rc::new(Const(1000000)))), Rc::new(Const(0)))));
    exp.eval().map(|val| println!("{}", val));
}
