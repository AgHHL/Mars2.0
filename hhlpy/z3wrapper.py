"""Wrapper for Z3 prover."""

from typing import Iterable, Optional
from decimal import Decimal
from fractions import Fraction
import z3

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import Expr
from ss2hcsp.hcsp.hcsp import Function


def convert(e: Expr, functions: dict[str, Function] = None) -> z3.ExprRef:
    """Conversion from expression to z3 expression."""
    if functions is None:
        functions = dict()

    if isinstance(e, expr.AVar):
        return z3.Real(e.name)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, int):
            return z3.RealVal(e.value)
        elif isinstance(e.value, (Decimal, Fraction)):
            return z3.RealVal(str(e.value))
        else:
            raise NotImplementedError(f"convert on {e.value} of type {type(e.value)}")
    elif isinstance(e, expr.BConst):
        return z3.BoolVal(e.value)
    elif isinstance(e, expr.FunExpr):
        if len(e.exprs) == 0:  # actually a constant
            return z3.Real(e.fun_name)
        else:
            f = functions[e.fun_name]
            return f(*[convert(e, functions) for e in e.exprs])
    elif isinstance(e, expr.LogicExpr):
        if e.op == '->':
            return z3.Implies(convert(e.exprs[0], functions), convert(e.exprs[1], functions))
        elif e.op == '&&':
            return z3.And(convert(e.exprs[0], functions), convert(e.exprs[1], functions))
        elif e.op == '||':
            return z3.Or(convert(e.exprs[0], functions), convert(e.exprs[1], functions))
        elif e.op == '<->':
            return convert(e.exprs[0], functions) == convert(e.exprs[1], functions)
        elif e.op == '!':
            return z3.Not(convert(e.exprs[0], functions))
        else:
            raise TypeError
    elif isinstance(e, expr.RelExpr):
        if e.op == '<':
            return convert(e.expr1, functions) < convert(e.expr2, functions)
        elif e.op == '<=':
            return convert(e.expr1, functions) <= convert(e.expr2, functions)
        elif e.op == '>':
            return convert(e.expr1, functions) > convert(e.expr2, functions)
        elif e.op == '>=':
            return convert(e.expr1, functions) >= convert(e.expr2, functions)
        elif e.op == '==':
            return convert(e.expr1, functions) == convert(e.expr2, functions)
        elif e.op == '!=':
            return z3.Not(convert(e.expr1, functions) == convert(e.expr2, functions))
    elif isinstance(e, expr.OpExpr):
        if len(e.exprs) == 1:
            return -convert(e.exprs[0], functions)
        elif e.op == '+':
            return convert(e.exprs[0], functions) + convert(e.exprs[1], functions)
        elif e.op == '-':
            return convert(e.exprs[0], functions) - convert(e.exprs[1], functions)
        elif e.op == '*':
            return convert(e.exprs[0], functions) * convert(e.exprs[1], functions)
        elif e.op == '/':
            return convert(e.exprs[0], functions) / convert(e.exprs[1], functions)
        elif e.op == '^':
            return convert(e.exprs[0], functions) ** convert(e.exprs[1], functions)
        else:
            raise NotImplementedError(f"convert on {e}")
    elif isinstance(e, expr.ExistsExpr):
        if isinstance(e.vars, tuple):
            return z3.Exists(list(convert(var, functions) for var in e.vars), convert(e.expr, functions))
        else:
            return z3.Exists(convert(e.vars, functions), convert(e.expr, functions))
    elif isinstance(e, expr.ForAllExpr):
        if isinstance(e.vars, tuple):
            return z3.ForAll(list(convert(var, functions) for var in e.vars), convert(e.expr, functions))
        else:
            return z3.ForAll(convert(e.vars, functions), convert(e.expr, functions))
    elif isinstance(e, expr.IfExpr):
        return z3.If(convert(e.cond, functions), convert(e.expr1, functions), convert(e.expr2, functions))
    else:
        print(e, type(e))
        raise NotImplementedError

def convertFunDecl(funDecl: Function, z3functions: dict[str, z3.FuncDeclRef]) -> tuple[z3.FuncDeclRef, z3.ExprRef]:
    """Convert list of function declarations.
    
    Parameters
    ----------
    funDecl: Function
        HCSP function to be converted.
    z3functions: dict[str, z3.FuncDeclRef]
        mapping of already converted functions.

    Returns
    -------
    f: z3.FuncDeclRef
        z3 function object.
    faxiom: z3.ExprRef
        z3 forall expression containing definition of the function.
    
    """
    convertedBody = convert(funDecl.expr, z3functions)
    f = z3.Function(funDecl.name, *[z3.RealSort() for v in funDecl.vars], convertedBody.sort())
    vars = [z3.Real(v) for v in funDecl.vars]
    return (f, z3.ForAll(vars, f(vars) == convertedBody))

def z3_prove(e: Expr, functions: dict[str, Function] = None) -> bool:
    """Attempt to prove the given condition using Z3.

    Return True if the statement can be proved, False if it cannot
    be proved.

    """
    if not functions:
        functions = dict()

    s = z3.Solver()
    z3functions: dict[str, z3.FuncDeclRef] = {}
    for f in functions:
        z3fun, faxiom = convertFunDecl(functions[f], z3functions)
        s.add(faxiom)
        z3functions[f] = z3fun
    s.add(z3.Not(convert(e, z3functions)))
    if str(s.check()) == 'unsat':
        return True
    else:
        return False

def z3_prove_gen(assums: Iterable[Expr], concl: Optional[Expr]) -> bool:
    """Attempt to prove the given statement using Z3."""

    s = z3.Solver()
    for assum in assums:
        s.add(convert(assum))
    if concl:
        s.add(z3.Not(convert(concl)))
    if str(s.check()) == "unsat":
        return True
    else:
        return False
