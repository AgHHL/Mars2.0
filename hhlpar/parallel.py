"""Assertions for reasoning about parallel programs."""

from typing import Iterable, List, Tuple, Union, Set
from sympy import sympify, degree, symbols, factor_list, fraction, simplify
from ss2hcsp.hcsp import hcsp, expr, assertion
from ss2hcsp.hcsp.parser import parse_hp_with_meta, parse_expr_with_meta
from hhlpar.wolframengine_wrapper import solveODE, wl_reduce, wl_reduce_true, wl_reduce_false, wl_prove, wl_proven
from hhlpar.wolframengine_wrapper import wl_simplify, wl_polynomial_div, wl_is_polynomial, found_wolfram, toWLexpr
import string

class EExpr:
    def priority(self) -> int:
        """Returns priority during printing."""
        raise NotImplementedError
    
    """Base class of extended expression used on assertions."""
    def substVar(self, var: str, expr: "EExpr") -> "EExpr":
        """Substitution of a variable by an expression.
        
        Default behavior is to return the corresponding VarSubstExpr.
        
        """
        return VarSubstExpr(self, var, expr)
    
    def substVars(self, vars, exprs) -> "EExpr":
        """Substitution of a variable by an expression.
        
        Default behavior is to return the corresponding VarSubstExpr.
        
        """
        return VarsSubstExpr(self, vars, exprs)


class BoundVar(EExpr):
    """Bound variables.
    
    The following are special bound variables for assertions:
    s0 : State - starting state
    s : State - ending state
    tr : Trace - accumulated trace

    The following are special bound variables for path invariants:
    s0 : State - starting state
    t : Real - time
    s : State - state at time t

    For parameterized assertions and quantifier expressions, name
    of bound variables are indicated within the assertion or expression.
    
    """
    def __init__(self, name: str):
        self.name = name

    def priority(self):
        return 100

    def __str__(self):
        return self.name
    

class VarExpr(EExpr):
    """Represents a variable in a state."""
    def __init__(self, name: str):
        self.name = name

    def priority(self):
        return 100

    def __str__(self):
        return self.name

    def substVar(self, var: str, expr: EExpr) -> EExpr:
        if var == self.name:
            return expr
        else:
            return self
        
    def substVars(self, vars, exprs) -> EExpr:
        g = self
        for i in range(len(vars)):
            if vars[i] == self.name:
                g = exprs[i]
        return g
        
class ConstExpr(EExpr):
    """Represents a constant number."""
    def __init__(self, val):
        self.val = val

    def priority(self):
        return 100
    
    def __str__(self):
        return str(self.val)
    
    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return self
    
    def substVars(self, vars, exprs) -> EExpr:
        return self
    

class VarSubstExpr(EExpr):
    """Substitution of a state on a variable."""
    def __init__(self, start_expr: EExpr, var: str, expr: EExpr):
        self.start_expr = start_expr
        self.var = var
        self.expr = expr

    def priority(self):
        return 100

    def __str__(self):
        return "%s[%s := %s]" % (self.start_expr, self.var, self.expr)
    
class VarsSubstExpr(EExpr):
    """Substitution of a state on a variable."""
    def __init__(self, start_expr: EExpr, vars, exprs):
        self.start_expr = start_expr
        self.vars = vars
        self.exprs = exprs

    def priority(self):
        return 100

    def __str__(self):
        G = ",".join(str(self.vars[i])+" := "+str(self.exprs[i]) for i in range(len(self.vars)))
        return "%s[%s]" % (self.start_expr, G)
        

class OpExpr(EExpr):
    """Operator."""
    def __init__(self, op: str, *exprs: EExpr):
        self.op = op
        self.exprs = tuple(exprs)

    def priority(self):
        if len(self.exprs) == 1:
            return 80
        elif self.op == '^':
            return 85
        elif self.op == '*' or self.op == '/' or self.op == '%':
            return 70
        else:
            return 65

    def __str__(self):
        if len(self.exprs) == 1:
            assert self.op == '-'
            s = str(self.exprs[0])
            if self.exprs[0].priority() < self.priority():
                s = '(' + s + ')'
            return '-' + s
        else:
            s1, s2 = str(self.exprs[0]), str(self.exprs[1])
            if self.exprs[0].priority() < self.priority():
                s1 = '(' + s1 + ')'
            if self.exprs[1].priority() <= self.priority():
                s2 = '(' + s2 + ')'
            if self.op == '^':
                return s1 + self.op + s2
            else:
                return s1 + ' ' + self.op + ' ' + s2

    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return OpExpr(self.op, *(sube.substVar(var, expr) for sube in self.exprs))
    
    def substVars(self, vars, exprs) -> EExpr:
        return OpExpr(self.op, *(sube.substVars(vars, exprs) for sube in self.exprs))
    
class BConstExpr(EExpr):
    """Represents a constant number."""
    def __init__(self, val: bool):
        self.val = val

    def priority(self):
        return 100

    def __str__(self):
        return "true" if self.val else "false"
    
    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return self
    
    def substVars(self, vars, exprs) -> EExpr:
        return self

true_eexpr = BConstExpr(True)
false_eexpr = BConstExpr(False)

class LogicExpr(EExpr):
    """Operator."""
    def __init__(self, op: str, *exprs: EExpr):
        self.op = op
        self.exprs = tuple(exprs)

    def priority(self):
        if self.op == '<->':
            return 25
        elif self.op == '->':
            return 20
        elif self.op == '&&':
            return 35
        elif self.op == '||':
            return 30
        elif self.op == '!':
            return 40
        else:
            raise NotImplementedError

    def __str__(self):
        if len(self.exprs) == 1:
            assert self.op == '!'
            s = str(self.exprs[0])
            if self.exprs[0].priority() < self.priority():
                s = '(' + s + ')'
            return '!' + s
        else:
            s1, s2 = str(self.exprs[0]), str(self.exprs[1])
            if self.exprs[0].priority() <= self.priority():
                s1 = '(' + s1 + ')'
            if self.exprs[1].priority() < self.priority():
                s2 = '(' + s2 + ')'
            return s1 + ' ' + self.op + ' ' + s2

    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return LogicExpr(self.op, *(sube.substVar(var, expr) for sube in self.exprs))
    
    def substVars(self, vars, exprs) -> EExpr:
        return LogicExpr(self.op, *(sube.substVars(vars, exprs) for sube in self.exprs))
    
class RelExpr(EExpr):
    """Operator."""
    def __init__(self, op: str, expr1: EExpr, expr2:EExpr):
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def priority(self):
        return 50

    def __str__(self):
        return "%s %s %s" % (self.expr1, self.op, self.expr2)

    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return RelExpr(self.op, self.expr1.substVar(var,expr), self.expr2.substVar(var,expr))
    
    def substVars(self, vars, exprs) -> EExpr:
        return RelExpr(self.op, self.expr1.substVars(vars,exprs), self.expr2.substVars(vars,exprs))

class IfExpr(EExpr):
    """If expressions."""
    def __init__(self, cond: EExpr, if_branch: EExpr, else_branch: EExpr):
        self.cond = cond
        self.if_branch = if_branch
        self.else_branch = else_branch

    def priority(self):
        return 100

    def __str__(self):
        return "(if %s then %s else %s)" % (self.cond, self.if_branch, self.else_branch)
    
    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return IfExpr(self.cond.substVar(var,expr), self.if_branch.substVar(var,expr), self.else_branch.substVar(var,expr))
    
    def substVars(self, vars, exprs) -> EExpr:
        return IfExpr(self.cond.substVars(vars,exprs), self.if_branch.substVars(vars,exprs), self.else_branch.substVars(vars,exprs))

class QuantExpr(EExpr):
    """Quantifier expressions."""
    def __init__(self, quantifier: str, bound_names: Iterable[str], expr: EExpr):
        self.quantifier = quantifier
        self.bound_names = bound_names
        self.expr = expr

    def __str__(self):
        return "%s%s. %s" % (self.quantifier, " ".join(self.bound_names), self.expr)
    
    
class ExistsExpr(EExpr):
    """Quantifier expressions."""
    def __init__(self, bound_names: Iterable[str], expr: EExpr):
        self.bound_names = bound_names
        self.expr = expr

    def priority(self):
        return 10

    def __str__(self):
        # print(type(self.bound_names))
        return "\exists %s. %s" % (" ".join(self.bound_names), self.expr)
    
    def substVar(self, var: str, expr: EExpr) -> EExpr:
        return ExistsExpr(self.bound_names, self.expr.substVar(var,expr))
    
    def substVars(self, vars, exprs) -> EExpr:
        return ExistsExpr(self.bound_names, self.expr.substVars(vars,exprs))

class cominf:

    def __init__(self):
        pass

    def __str__(self):
        raise NotImplementedError 


class Ininf(cominf):
    
    def __init__(self, ch_name: str):
        self.ch_name = ch_name
        
    def __str__(self):
        return "%s?" % (self.ch_name)
    
class Outinf(cominf):
    
    def __init__(self, ch_name: str, expr: EExpr):
        self.ch_name = ch_name
        self.expr = expr

    def __str__(self):
        return "%s!%s" % (self.ch_name, self.expr)

class Assertion:
    """Base class for assertion for parallel programs.
    
    Each assertion is interpreted as a predicate on (s0, s, tr), where
    s0 is the starting state, s is the ending state, and tr is the
    accumulated trace.
    
    """
    def substVar(self, var: str, expr: EExpr) -> "Assertion":
        """Substitute given variable for an expression.
        
        The default implementation returns the VarSubstAssersion. Concrete
        assertions can choose to simplify the substitution.
        
        """
        return VarSubstAssertion(self, var, expr)
    
    def substVars(self, vars, exprs) -> "Assertion":
        """Substitute given variables for an expression.
        
        The default implementation returns the VarSubstAssersion. Concrete
        assertions can choose to simplify the substitution.
        
        """
        return VarsSubstAssertion(self, vars, exprs)

class InitAssertion(Assertion):
    """Assertion representing initial state.
    
    The interpretation is: s == s0 && tr = [].
    
    """
    def __init__(self):
        pass

    def __str__(self):
        return "init"
    
    def substVal(self, var: str, expr: EExpr) -> "Assertion":
        return self
    
class FalseAssertion(Assertion):
    """Assertion representing False.
    
    The interpretation is no s and tr satisfied.
    
    """
    def __init__(self):
        pass

    def __str__(self):
        return "false"
    
    def substVar(self, var: str, expr: EExpr) -> "Assertion":
        return self
    
    def substVars(self, vars, exprs) -> "Assertion":
        return self
    
    def substVal(self, var: str, expr: EExpr) -> "Assertion":
        return self
    
class TrueAssertion(Assertion):
    """Assertion representing False.
    
    The interpretation is all s and tr satisfied.
    
    """
    def __init__(self):
        pass

    def __str__(self):
        return "true"
    
    def substVar(self, var: str, expr: EExpr) -> "Assertion":
        return self
    
    def substVars(self, vars, exprs) -> "Assertion":
        return self
    
    def substVal(self, var: str, expr: EExpr) -> "Assertion":
        return self
    
class VarSubstAssertion(Assertion):
    """Obtaining a new assertion by substitution of a variable.
    
    The interpretation is to perform the substitution on the starting
    state.
    
    """
    def __init__(self, start_assn: Assertion, var: str, expr: EExpr):
        self.start_assn = start_assn
        self.var = var
        self.expr = expr

    def __str__(self):
        return "%s[%s := %s]" % (self.start_assn, self.var, self.expr)
    
    def substVal(self, var: str, expr: EExpr) -> "Assertion":
        return VarSubstAssertion(self.start_assn.substVal(var,expr), self.var, self.expr.substVar(var,expr))
    
class VarsSubstAssertion(Assertion):
    """Obtaining a new assertion by substitution of a variable.
    
    The interpretation is to perform the substitution on the starting
    state.
    
    """
    def __init__(self, start_assn: Assertion, vars, exprs):
        self.start_assn = start_assn
        self.vars = vars
        self.exprs = exprs

    def __str__(self):
        G = ",".join(str(self.vars[i])+" := "+str(self.exprs[i]) for i in range(len(self.vars)))
        return "%s[%s]" % (self.start_assn,G)
    
    def substVal(self, var: str, expr: EExpr) -> "Assertion":
        l = []
        for sube in self.exprs:
            l.append(sube.substVar(var,expr))
        return VarsSubstAssertion(self.start_assn.substVal(var,expr), self.vars, l)

class OpAssn(Assertion):
    """Operators acting on assertions."""
    def __init__(self, op: str, *assns: Assertion):
        self.op = op
        self.assns = tuple(assns)

    def __str__(self):
        if len(self.assns) == 1:
            return "%s%s" % (self.op, self.assns[0])
        else:
            if self.op =="||":
                return "(%s \u142F %s)" % (self.assns[0], self.assns[1])
            else:
                return "%s %s %s" % (self.assns[0], self.op, self.assns[1])
        
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        return OpAssn(self.op, *(assn.substVar(var, expr) for assn in self.assns))
    
    def substVars(self, vars, exprs) -> Assertion:
        return OpAssn(self.op, *(assn.substVars(vars, exprs) for assn in self.assns))
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        return OpAssn(self.op, *(assn.substVal(var, expr) for assn in self.assns))

class RecursionVar(Assertion):
    """Recursion variable."""
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return self.name
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        return self

class RecAssertion(Assertion):
    """Assertion defined by recursion."""
    def __init__(self, rec_var: str, assn: Assertion):
        self.rec_var = rec_var
        self.assn = assn

    def __str__(self):
        return "(rec %s. %s)" % (self.rec_var, self.assn)
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        return RecAssertion(self.rec_var, self.assn.substVal(var, expr))

class ParamAssertion:
    """Parameterized assertions.
    
    Possible parameters include:
    d : Real - delay time
    v : Real -> communicated value.
    
    """
    def __init__(self, bound_names: Iterable[str], assn: Assertion):
        self.bound_names = bound_names
        self.assn = assn

    def __str__(self):
        if len(self.bound_names) == 1:
            return "{%s => %s}" % (self.bound_names[0], self.assn)
        else:
            return "{(%s) => %s}" % (', '.join(self.bound_names), self.assn)
        
    def substVar(self, var: str, expr: EExpr) -> "ParamAssertion":
        """Substitution of a variable by an expression."""
        return ParamAssertion(self.bound_names, self.assn.substVar(var, expr))
    
    def substVars(self, vars, exprs) -> "ParamAssertion":
        """Substitution of a variable by an expression."""
        return ParamAssertion(self.bound_names, self.assn.substVars(vars, exprs))
    
    def substVal(self, var: str, expr: EExpr) -> "ParamAssertion":
        """Substitution of a variable by an expression."""
        return ParamAssertion(self.bound_names, self.assn.substVal(var, expr))

class PathInvariant:
    """Base class of properties satisfied by a path.
    
    Each path invariant is interpreted as a predicate on (s0, t, s),
    where s0 is the starting state, t is the time, and s is the state
    reached at time t.
    
    """
    def substVar(self, var: str, expr: EExpr) -> "PathInvariant":
        return SubstVarPathInvariant(self, var, expr)
    
    def substVars(self, vars, exprs) -> "PathInvariant":
        return SubstVarsPathInvariant(self, vars, exprs)

class IdPathInvariant(PathInvariant):
    """Identity path invariant.
    
    The interpretation is: s = s0 (for all time t).
    """
    def __init__(self):
        pass

    def __str__(self):
        return "id_inv"
    
    def substVar(self, var: str, expr: EExpr) -> PathInvariant:
        return ExprPathInvariant(OpExpr("==", BoundVar("s"), BoundVar("s0"))).substVar(var, expr)
    
    def substVars(self, vars, exprs) -> PathInvariant:
        return ExprPathInvariant(OpExpr("==", BoundVar("s"), BoundVar("s0"))).substVars(vars, exprs)
    
    def substVal(self, var, expr) -> PathInvariant:
        return self
    

class ExprPathInvariant(PathInvariant):
    """Path invariant specified by an expression.
    
    The expression contains special variables: s0, s and t.
    
    """
    def __init__(self, expr: EExpr):
        self.expr = expr

    def __str__(self):
        return str(self.expr)
    
    def substVal(self, var, expr) -> PathInvariant:
        return self

class ODEPathInvariant(PathInvariant):
    """Path invariant specified by an ODE inv. We record the ODE"""
    def __init__(self, expr: EExpr, eqs: List[Tuple[str, expr.Expr]], sols: Tuple[List[str], List[EExpr]], unsol: str, cons: EExpr, pn = None):
        self.expr = expr
        self.eqs = eqs
        self.sols = (sols[0].copy(), sols[1].copy())
        self.unsol = unsol
        self.cons = cons
        self.pn = pn

    def __str__(self):
        return str(self.expr)
    
    def substVal(self, var, expr) -> PathInvariant:
        l = []
        for t in self.sols[1]:
            l.append(t.substVar(var,expr))
        return ODEPathInvariant(self.expr, self.eqs, (self.sols[0],l), self.unsol, self.cons, self.pn)

class SubstVarPathInvariant(PathInvariant):
    """Substituting a variable in a path invariant."""
    def __init__(self, start_path_inv: PathInvariant, var: str, expr: EExpr):
        self.start_path_inv = start_path_inv
        self.var = var
        self.expr = expr

    def __str__(self):
        return "%s[%s := %s]" % (self.start_path_inv, self.var, self.expr)
    
    def substVal(self, var, expr) -> PathInvariant:
        return SubstVarPathInvariant(self.start_path_inv.substVal(var,expr), self.var, self.expr.substVar(var,expr))
    
class SubstVarsPathInvariant(PathInvariant):
    """Substituting a variable in a path invariant."""
    def __init__(self, start_path_inv: PathInvariant, vars, exprs):
        self.start_path_inv = start_path_inv
        self.vars = vars
        self.exprs = exprs

    def __str__(self):
        G = ",".join(str(self.vars[i])+" := "+str(self.exprs[i]) for i in range(len(self.vars)))
        return "%s[%s]" % (self.start_path_inv, G)
    
    def substVal(self, var, expr) -> PathInvariant:
        l = []
        for sube in self.exprs:
            l.append(sube.substVar(var, expr))
        return SubstVarsPathInvariant(self.start_path_inv.substVal(var,expr), self.vars, l)

class PPathInvariant(PathInvariant):
    def __init__(self, path_inv1: PathInvariant, path_inv2: PathInvariant):
        self.path_inv1 = path_inv1
        self.path_inv2 = path_inv2

    def __str__(self) -> str:
        return "%s\u1431%s" % (self.path_inv1, self.path_inv2)
    
    def substVar(self, var: str, expr: EExpr) -> PathInvariant:
        return PPathInvariant(self.path_inv1.substVar(var,expr),self.path_inv2.substVar(var,expr))
    
    def substVars(self, vars, exprs) -> PathInvariant:
        return PPathInvariant(self.path_inv1.substVars(vars,exprs),self.path_inv2.substVars(vars,exprs))
    
    def substVal(self, var, expr) -> PathInvariant:
        return PPathInvariant(self.path_inv1.substVal(var,expr),self.path_inv2.substVal(var,expr))

class PureAssertion(Assertion):
    def __init__(self, expr: EExpr, assn: Assertion):
        self.expr = expr
        self.assn = assn
        

    def __str__(self):
        return "(\u2191(%s) \u1431 %s)" % (self.expr, self.assn)
    
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        return PureAssertion(self.expr.substVar(var,expr), self.assn.substVar(var,expr))
    
    def substVars(self, vars, exprs) -> Assertion:
        return PureAssertion(self.expr.substVars(vars,exprs), self.assn.substVars(vars,exprs))
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        return PureAssertion(self.expr.substVar(var,expr), self.assn.substVal(var,expr))

class WaitInAssertion(Assertion):
    """Wait-in assertion.
    
    Syntax for wait-in assertion is:

        wait_in(path_inv, ch, {(d, v) => assn})

    The components are path invariant, channel of communication, and the
    ensuing assertion, respectively.

    """
    def __init__(self, path_inv: PathInvariant, ch_name: str, param_assn: ParamAssertion):
        self.path_inv = path_inv
        self.ch_name = ch_name
        assert len(param_assn.bound_names) == 2
        self.param_assn = param_assn

    def __str__(self):
        return "wait_in(%s, %s, %s)" % (self.path_inv, self.ch_name, self.param_assn)
    
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        return WaitInAssertion(self.path_inv.substVar(var, expr), self.ch_name,
                                self.param_assn.substVar(var, expr))
    
    def substVars(self, vars, exprs) -> Assertion:
        return WaitInAssertion(self.path_inv.substVars(vars, exprs), self.ch_name,
                                self.param_assn.substVars(vars, exprs))
    
    def substVal(self, var: str, expr: EExpr) -> "Assertion":
        return WaitInAssertion(self.path_inv.substVal(var,expr),self.ch_name, self.param_assn.substVal(var, expr))
    
    def delay(self, expr: EExpr) -> "Assertion":
        return WaitInAssertion(self.path_inv.substVal("t",OpExpr("+",VarExpr("t"),expr)),self.ch_name, self.param_assn.substVal(self.param_assn.bound_names[0], OpExpr("+",VarExpr(self.param_assn.bound_names[0]),expr)))
    


class WaitOutAssertion(Assertion):
    """Wait-out assertion.
    
    Syntax for wait-out assertion is:

        wait_out(path_inv, ch, {(d, v) => assn})

    The components are path invariant, channel of communication, and the
    ensuing assertion, respectively.
    
    """
    def __init__(self, path_inv: PathInvariant, ch_name: str, param_assn: ParamAssertion):
        self.path_inv = path_inv
        self.ch_name = ch_name
        assert len(param_assn.bound_names) == 2
        self.param_assn = param_assn

    def __str__(self):
        return "wait_out(%s, %s, %s)" % (self.path_inv, self.ch_name, self.param_assn)
    

class WaitOutvAssertion(Assertion):
    """Wait-outv assertion.
    
    Syntax for wait-outv assertion is:

        wait_outv(path_inv, ch, e, {d => assn})

    The components are path invariant, channel of communication, expression
    for the value sent, and the ensuing assertion.
    
    """
    def __init__(self, path_inv: PathInvariant, ch_name: str, expr: EExpr, param_assn: ParamAssertion):
        self.path_inv = path_inv
        self.ch_name = ch_name
        self.expr = expr
        assert len(param_assn.bound_names) == 1
        self.param_assn = param_assn

    def __str__(self):
        return "wait_outv(%s, %s, %s, %s)" % (self.path_inv, self.ch_name, self.expr, self.param_assn)
    
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        return WaitOutvAssertion(self.path_inv.substVar(var, expr), self.ch_name,
                                 self.expr.substVar(var, expr), self.param_assn.substVar(var, expr))
    
    def substVars(self, vars, exprs) -> Assertion:
        return WaitOutvAssertion(self.path_inv.substVars(vars, exprs), self.ch_name,
                                 self.expr.substVars(vars, exprs), self.param_assn.substVars(vars, exprs))
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        return WaitOutvAssertion(self.path_inv.substVal(var, expr), self.ch_name,
                                 self.expr.substVar(var, expr), self.param_assn.substVal(var, expr))
    
    def delay(self, expr: EExpr) -> "Assertion":
        return WaitOutvAssertion(self.path_inv.substVal("t",OpExpr("+",VarExpr("t"),expr)),self.ch_name, self.expr, self.param_assn.substVal(self.param_assn.bound_names[0], OpExpr("+",VarExpr(self.param_assn.bound_names[0]),expr)))
    

class WaitIn0Assertion(Assertion):
    """Wait-in0 assertion.

    Version of wait-in assuming immediate communication. The syntax is:

        wait_in0(path_inv, ch, {v => assn})

    The components are path invariant, channel of communication, and the
    ensuing assertion.

    TODO: investigate whether path_inv is necessary in this case.
    
    """
    def __init__(self, path_inv: PathInvariant, ch_name: str, param_assn: ParamAssertion):
        self.path_inv = path_inv
        self.ch_name = ch_name
        assert len(param_assn.bound_names) == 1
        self.param_assn = param_assn

    def __str__(self):
        return "wait_in0(%s, %s, %s)" % (self.path_inv, self.ch_name, self.param_assn)

class  WaitAssertion(Assertion):
    """Wait assertion.
    
    Syntax for wait assertion is:

        wait(path_inv, e, {(d => assn)})

    The components are path invariant, expression for delay time, and the
    ensuing assertion.

    """
    def __init__(self, path_inv: PathInvariant, delay_expr: EExpr, param_assn: ParamAssertion):
        self.path_inv = path_inv
        self.delay_expr = delay_expr
        assert len(param_assn.bound_names) == 1
        self.param_assn = param_assn

    def __str__(self):
        return "wait(%s, %s, %s)" % (self.path_inv, self.delay_expr, self.param_assn)
    
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        return WaitAssertion(self.path_inv.substVar(var, expr), 
                                 self.delay_expr.substVar(var, expr), self.param_assn.substVar(var, expr))
    
    def substVars(self, vars, exprs) -> Assertion:
        return WaitAssertion(self.path_inv.substVars(vars, exprs), 
                                 self.delay_expr.substVars(vars, exprs), self.param_assn.substVars(vars, exprs))
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        return WaitAssertion(self.path_inv.substVal(var, expr),
                                 self.delay_expr.substVar(var, expr), self.param_assn.substVal(var, expr))
    
    def delay(self, expr: EExpr) -> "Assertion":
        return WaitAssertion(self.path_inv.substVal("t",OpExpr("+",VarExpr("t"),expr)), OpExpr("-", self.delay_expr, expr), self.param_assn.substVal(self.param_assn.bound_names[0], OpExpr("+",VarExpr(self.param_assn.bound_names[0]),expr)))
    
    

class InterruptAssertion(Assertion):
    
    def __init__(self, path_inv: PathInvariant, delay_expr: EExpr, param_assn: ParamAssertion, comm_specs):
        self.path_inv = path_inv
        self.delay_expr = delay_expr
        assert len(param_assn.bound_names) == 1
        self.param_assn = param_assn
        for comm_spec in comm_specs:
            assert isinstance(comm_spec, tuple) and len(comm_spec) == 2
            assert isinstance(comm_spec[0], cominf) and isinstance(comm_spec[1], ParamAssertion)
        self.comm_specs: List[Tuple[cominf, Assertion]] = comm_specs

    def __str__(self):
        str_comms = ", ".join(str(comm_hp) + " --> " + str(out_assn) for comm_hp, out_assn in self.comm_specs)
        return "interrupt(%s, %s, %s, (%s))" % (self.path_inv, self.delay_expr, self.param_assn, str_comms)
    
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVar(var, expr)))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVar(var, expr)),out_assn.substVar(var, expr)))
            else:
                raise NotImplementedError

        return InterruptAssertion(self.path_inv.substVar(var, expr), 
                                 self.delay_expr.substVar(var, expr), self.param_assn.substVar(var, expr),comm_specs)
    
    def substVars(self, vars, exprs) -> Assertion:
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVars(vars, exprs)))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVars(vars, exprs)),out_assn.substVars(vars, exprs)))
            else:
                raise NotImplementedError

        return InterruptAssertion(self.path_inv.substVars(vars, exprs), 
                                 self.delay_expr.substVars(vars, exprs), self.param_assn.substVars(vars, exprs),comm_specs)
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVal(var, expr)))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVar(var, expr)),out_assn.substVal(var, expr)))
            else:
                raise NotImplementedError

        return InterruptAssertion(self.path_inv.substVal(var, expr), 
                                 self.delay_expr.substVar(var, expr), self.param_assn.substVal(var, expr),comm_specs)
    
    def delay(self, expr: EExpr) -> "Assertion":
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVal(out_assn.bound_names[0], OpExpr("+",VarExpr(out_assn.bound_names[0]),expr))))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVar(out_assn.bound_names[0], OpExpr("+",VarExpr(out_assn.bound_names[0]),expr))),out_assn.substVal(out_assn.bound_names[0], OpExpr("+",VarExpr(out_assn.bound_names[0]),expr))))
            else:
                raise NotImplementedError
        return InterruptAssertion(self.path_inv.substVal("t",OpExpr("+",VarExpr("t"),expr)), OpExpr("-", self.delay_expr, expr), self.param_assn.substVal(self.param_assn.bound_names[0], OpExpr("+",VarExpr(self.param_assn.bound_names[0]),expr)),comm_specs)
    
    def cond(self) -> "InterruptAssertion":
        return InterruptAssertion(self.path_inv, self.delay_expr, ParamAssertion(self.param_assn.bound_names,PureAssertion(RelExpr("<",ConstExpr(0),self.delay_expr),self.param_assn.assn)), self.comm_specs)
 
class InterruptinfAssertion(Assertion):
    def __init__(self, path_inv: PathInvariant, comm_specs):
        self.path_inv = path_inv
        for comm_spec in comm_specs:
            assert isinstance(comm_spec, tuple) and len(comm_spec) == 2
            assert isinstance(comm_spec[0], cominf) and isinstance(comm_spec[1], ParamAssertion)
        self.comm_specs: List[Tuple[hcsp.HCSP, Assertion]] = comm_specs

    def __str__(self):
        str_comms = ", ".join(str(comm_hp) + " --> " + str(out_assn) for comm_hp, out_assn in self.comm_specs)
        return "interruptinf(%s, (%s))" % (self.path_inv, str_comms)
    
    def substVar(self, var: str, expr: EExpr) -> Assertion:
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVar(var, expr)))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVar(var, expr)),out_assn.substVar(var, expr)))
            else:
                raise NotImplementedError

        return InterruptinfAssertion(self.path_inv.substVar(var, expr), comm_specs)
    
    def substVars(self, vars, exprs) -> Assertion:
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVars(vars, exprs)))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVars(vars, exprs)),out_assn.substVars(vars, exprs)))
            else:
                raise NotImplementedError

        return InterruptinfAssertion(self.path_inv.substVars(vars, exprs), comm_specs)
    
    def substVal(self, var: str, expr: EExpr) -> Assertion:
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVal(var, expr)))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVar(var, expr)),out_assn.substVal(var, expr)))
            else:
                raise NotImplementedError

        return InterruptinfAssertion(self.path_inv.substVal(var, expr), comm_specs)
    
    def delay(self, expr: EExpr) -> "Assertion":
        comm_specs = []
        for comm_hp, out_assn in self.comm_specs:
            if isinstance(comm_hp,Ininf):
                comm_specs.append((comm_hp,out_assn.substVal(out_assn.bound_names[0], OpExpr("+",VarExpr(out_assn.bound_names[0]),expr))))
            elif isinstance(comm_hp,Outinf): 
                comm_specs.append((Outinf(comm_hp.ch_name,comm_hp.expr.substVar(out_assn.bound_names[0], OpExpr("+",VarExpr(out_assn.bound_names[0]),expr))),out_assn.substVal(out_assn.bound_names[0], OpExpr("+",VarExpr(out_assn.bound_names[0]),expr))))
            else:
                raise NotImplementedError
        return InterruptinfAssertion(self.path_inv.substVal("t",OpExpr("+",VarExpr("t"),expr)), comm_specs)
    

init = InitAssertion()
Fassn = FalseAssertion()
Tassn = TrueAssertion()
id_inv = IdPathInvariant()

def expr_to_eexpr(e: expr.Expr) -> EExpr:
    """Convert expr in HCSP to EExpr."""
    if isinstance(e, expr.AVar):
        return VarExpr(e.name)
    elif isinstance(e, expr.AConst):
        return ConstExpr(e.value)
    elif isinstance(e,expr.BConst):
        return BConstExpr(e.value)
    elif isinstance(e, expr.OpExpr):
        return OpExpr(e.op, *(expr_to_eexpr(sube) for sube in e.exprs))
    elif isinstance(e, expr.LogicExpr):
        return LogicExpr(e.op, *(expr_to_eexpr(sube) for sube in e.exprs))
    elif isinstance(e, expr.RelExpr):
        return RelExpr(e.op, expr_to_eexpr(e.expr1), expr_to_eexpr(e.expr2))
    elif isinstance(e,expr.IfExpr):
        return IfExpr(expr_to_eexpr(e.cond), expr_to_eexpr(e.expr1), expr_to_eexpr(e.expr2))
    elif isinstance(e,expr.ExistsExpr):
        return ExistsExpr([s.name for s in e.vars], expr_to_eexpr(e.expr))
    else:
        # print(e)
        raise NotImplementedError
    
def eexpr_to_expr(e: EExpr) -> expr.Expr:
    """Convert EExpr to expr in HCSP."""
    if isinstance(e, VarExpr):
        return expr.AVar(e.name)
    elif isinstance(e, ConstExpr):
        return expr.AConst(e.val)
    elif isinstance(e, BConstExpr):
        return expr.BConst(e.val)
    elif isinstance(e, OpExpr):
        return expr.OpExpr(e.op, *(eexpr_to_expr(sube) for sube in e.exprs))
    elif isinstance(e, LogicExpr):
        return expr.LogicExpr(e.op, *(eexpr_to_expr(sube) for sube in e.exprs))
    elif isinstance(e, RelExpr):
        return expr.RelExpr(e.op, eexpr_to_expr(e.expr1), eexpr_to_expr(e.expr2))
    elif isinstance(e, IfExpr):
        return expr.IfExpr(eexpr_to_expr(e.cond), eexpr_to_expr(e.if_branch), eexpr_to_expr(e.else_branch))
    elif isinstance(e, ExistsExpr):
        return expr.ExistsExpr(e.bound_names,eexpr_to_expr(e.expr))
    else:
        raise NotImplementedError

def compute_closure(e):
    """Compute the closure for an open interval"""
    if isinstance(e, expr.RelExpr):
        if e.op == '<':
            return expr.RelExpr("<=", e.expr1, e.expr2)
        elif e.op == '>':
            return expr.RelExpr(">=", e.expr1, e.expr2)
        elif e.op == '!=':
            return expr.true_expr
        else:
            raise NotImplementedError

    elif isinstance(e, expr.LogicExpr):
        if e.op == '&&':
            return expr.LogicExpr('&&', compute_closure(e.exprs[0]), compute_closure(e.exprs[1]))
        elif e.op == '||':
            return expr.LogicExpr('||', compute_closure(e.exprs[0]), compute_closure(e.exprs[1]))
        elif e.op == '!':
            return compute_closure(expr.neg_expr(e.exprs[0]))
        else:
            raise NotImplementedError

    else:
        raise NotImplementedError
    
def compute_boundary(e):
    # Compute the boundary for a boolean expression.
    # Example: e is x < 0 && y < 0, then compute_boundary returns 
    # x == 0 && y <= 0 || y == 0 && x <= 0
    if isinstance(e, expr.RelExpr):
        if e.op in ['<', '>', '!=']:
            return expr.RelExpr("==", e.expr1, e.expr2)
    
    elif isinstance(e, expr.LogicExpr):
        if e.op == '&&':
            conjs = expr.split_conj(e)
            conj_boundarys = []
            conj_closure = []
            # Compute the boundary and closure for each conjuncts
            # Example, conj_boundarys for x < 0 && y < 0 is [x == 0, y == 0]
            #          conj_closure for x < 0 && y < 0 is [x <= 0, y <= 0]
            for c in conjs:
                conj_boundarys.append(compute_boundary(c))
                conj_closure.append(compute_closure(c))
            
            boundarys = []
            for i in range(len(conjs)):
                # The boundary of ith conjunct. 
                # Note that other conjuncts' boundaries may also be satisfied, 
                # so here use closure of other conjuncts.
                sub_boundarys = conj_closure.copy() 
                # Example, sub_boundarys is [x <= 0, y <= 0]
                sub_boundarys[i] = conj_boundarys[i]    
                # Example, sub_boundarys when i == 0 is [x == 0, y <= 0]
                sub_boundary = expr.list_conj(*sub_boundarys) 
                # Example, sub_boundarys when i == 0 is x == 0 && y <= 0

                boundarys.append(sub_boundary)
            return expr.list_disj(*boundarys) # Example, returns x == 0 && y <= 0 || y == 0 && x <= 0
        elif e.op == '||':
            boundary1 = compute_boundary(e.exprs[0])
            boundary2 = compute_boundary(e.exprs[1])
            neg1 = expr.neg_expr(e.exprs[0])
            neg2 = expr.neg_expr(e.exprs[1])
            disj1 = expr.LogicExpr('&&', neg1, boundary2)
            disj2 = expr.LogicExpr('&&', neg2, boundary1)
            return expr.LogicExpr('||', disj1, disj2)
        elif e.op == '!':
            return compute_boundary(expr.neg_expr(e.exprs[0]))
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError
    
def compute_diff(e, eqs_dict, functions):
    """Compute differential of an arithmetic or boolean expression."""
    def rec(e):
        if isinstance(e, expr.LogicExpr):
            if e.op == "&&":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "||":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "->":
                return rec(expr.LogicExpr("||", expr.neg_expr(e.exprs[0]), e.exprs[1]))
            elif e.op == "!":
                return rec(expr.neg_expr(e.exprs[0]))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.RelExpr):
            if e.op == '<' or e.op == '<=':
                return expr.RelExpr("<=", rec(e.expr1), rec(e.expr2))
            elif e.op == '>' or e.op == '>=':
                return expr.RelExpr(">=", rec(e.expr1), rec(e.expr2))
            elif e.op == '==' or e.op == '!=':
                return expr.RelExpr("==", rec(e.expr1), rec(e.expr2))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.AConst):
            return expr.AConst(0)
        elif isinstance(e, expr.BConst):
            return expr.BConst(True)
        elif isinstance(e, expr.FunExpr):
            if len(e.exprs) == 0:
                return expr.AConst(0)      
            elif e.fun_name in functions:
                return rec(expr.replace_function(e, functions))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.AVar):
            if e.name in eqs_dict:
                return eqs_dict[e.name]
            else:
                return expr.AConst(0)
        elif isinstance(e, expr.OpExpr):
            if len(e.exprs) == 1:
                return expr.OpExpr("-", rec(e.exprs[0]))
            elif e.op == '+':
                return expr.OpExpr("+", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '-':
                return expr.OpExpr("-", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '*':
                # d(u*v) = u*dv + du*v
                du, dv = rec(e.exprs[0]), rec(e.exprs[1])
                return expr.OpExpr("+", expr.OpExpr("*", e.exprs[0], dv), 
                                        expr.OpExpr("*", du, e.exprs[1]))
            elif e.op == '^' and isinstance(e.exprs[1], expr.AConst):
                # d(u^n) = n * u^(n-1) * du
                du = rec(e.exprs[0])
                mid_expr = expr.OpExpr("^", e.exprs[0], expr.OpExpr("-", e.exprs[1], expr.AConst(1)))
                return expr.OpExpr("*", e.exprs[1], expr.OpExpr("*", mid_expr, du)) 
            elif e.op == '/':
                # d(u/v) = (du * v - u * dv)/ v^2   u'v-uv')/v²
                # If v is constant, d(u/v) = 1/v * du, which is easier than using above rule.
                if isinstance(e.exprs[1], expr.AConst) or \
                   isinstance(e.exprs[1], expr.FunExpr) and len(e.exprs == 0): # actually a constant
                    du = rec(e.exprs[0])
                    return expr.OpExpr('*', expr.OpExpr('/', expr.AConst(1), e.exprs[1]), du)
                else:
                    du = rec(e.exprs[0])
                    dv = rec(e.exprs[1])
                    numerator = expr.OpExpr("-", expr.OpExpr("*", du, e.exprs[1]), expr.OpExpr("*", e.exprs[0], dv))
                    denominator = expr.OpExpr('*', e.exprs[1], e.exprs[1])
                    return expr.OpExpr('/', numerator, denominator)            
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    return rec(e)

def variant_name(vars: List[str], prefix: str) -> str:
    i = 1
    while prefix + str(i) in vars:
        i += 1
    vars.append(prefix + str(i))
    return prefix + str(i)
 
def OpAssn_mult(op,assn_list):
    if len(assn_list)==0:
        raise NotImplementedError
    elif len(assn_list)==1:
        return assn_list[0]
    else:
        return OpAssn(op,assn_list[0],OpAssn_mult(op,assn_list[1:]))
    
def LogicExpr_mult(op,expr_list):
    if len(expr_list)==0:
        if op == "&&":
            return true_eexpr
        elif op == "||":
            return false_eexpr
        else:
            raise NotImplementedError
    elif len(expr_list)==1:
        return expr_list[0]
    else:
        return LogicExpr(op,expr_list[0],LogicExpr_mult(op,expr_list[1:]))

def seq_hcsp_to_assn_gen(hp: hcsp.HCSP, remain: Assertion, bound_vars: List[str]) -> Assertion:
    """Obtain assertion for sequential HCSP programs."""
    if isinstance(hp, hcsp.Skip):
        return remain
    elif isinstance(hp, hcsp.Assign):
        return remain.substVar(hp.var_name.name, expr_to_eexpr(hp.expr))
    elif isinstance(hp, hcsp.InputChannel):
        dname, vname = variant_name(bound_vars, "d"), variant_name(bound_vars, "v")
        return WaitInAssertion(id_inv, hp.ch_name.name,
                               ParamAssertion([dname, vname],
                                              remain.substVar(hp.var_name.name, VarExpr(vname))))
    elif isinstance(hp, hcsp.OutputChannel):
        dname = variant_name(bound_vars, "d")
        return WaitOutvAssertion(id_inv, hp.ch_name.name, expr_to_eexpr(hp.expr),
                                 ParamAssertion([dname], remain))
    elif isinstance(hp, hcsp.Wait):
        dname = variant_name(bound_vars, "d")
        return WaitAssertion(id_inv, expr_to_eexpr(hp.delay),
                             ParamAssertion([dname], remain))
    elif isinstance(hp, hcsp.Sequence):
        raise AssertionError
    else:
        raise NotImplementedError

# def seq_hcsp_to_assn(hp: hcsp.HCSP) -> Assertion:
#     bound_vars = []

#     def rec(hp):
#         nonlocal bound_vars
#         if isinstance(hp, hcsp.Sequence):
#             if len(hp.hps) == 1:
#                 return rec(hp.hps[0])
#             else:
#                 Q = rec(hcsp.Sequence(*(hp.hps[1:])))
#                 return seq_hcsp_to_assn_gen(hp.hps[0], Q, bound_vars)
#         else:
#             return seq_hcsp_to_assn_gen(hp, init, bound_vars)

#     return rec(hp)


# def seq_hcsp_to_assn(hp: hcsp.HCSP) -> Assertion:
#     bound_vars = []

#     def rec(hp, remain: Assertion):
#         nonlocal bound_vars
#         if isinstance(hp, hcsp.Sequence):
#             if len(hp.hps) == 1:
#                 return rec(hp.hps[0], remain)
#             else:
#                 Q = rec(hcsp.Sequence(*(hp.hps[1:])), remain)
#                 return seq_hcsp_to_assn_gen(hp.hps[0], Q, bound_vars)
#         elif isinstance(hp, hcsp.Loop):
#             Rname = variant_name(bound_vars, "R")
#             Q = rec(hp.hp, RecursionVar(Rname))
#             return RecAssertion(Rname,Q)
#         else:
#             return seq_hcsp_to_assn_gen(hp, remain, bound_vars)

#     return rec(hp, init)

def seq_hcsp_to_assn(hp: hcsp.HCSP) -> Assertion:
    bound_vars = []

    def rec(hp, remain: Assertion):
        nonlocal bound_vars
        if isinstance(hp, hcsp.Sequence):
            if len(hp.hps) == 1:
                return rec(hp.hps[0], remain)
            else:
                Q = rec(hcsp.Sequence(*(hp.hps[1:])), remain)
                return rec(hp.hps[0], Q)
        elif isinstance(hp, hcsp.Loop):
            Rname = variant_name(bound_vars, "R")
            Q = rec(hp.hp, RecursionVar(Rname))
            P = OpAssn("||", remain, Q)
            return RecAssertion(Rname,P)
        elif isinstance(hp, hcsp.Skip):
            return remain
        elif isinstance(hp, hcsp.IChoice):
            P = []
            for hhp in hp.hps:
                P.append(rec(hhp,remain))
            return OpAssn_mult("||",P)
        elif isinstance(hp, hcsp.ITE):
            if len(hp.if_hps)==0:
                raise NotImplementedError
            else:
                p = expr_to_eexpr(hp.if_hps[0][0])
                P = [PureAssertion(p,rec(hp.if_hps[0][1],remain))]
                p = LogicExpr("!",p)
                for i in range(1,len(hp.if_hps)):
                    q = LogicExpr("&&",p,expr_to_eexpr(hp.if_hps[i][0]))
                    P.append(PureAssertion(q,rec(hp.if_hps[i][1],remain)))
                    p = LogicExpr("&&",p,LogicExpr("!",expr_to_eexpr(hp.if_hps[i][0])))
                if isinstance(hp.else_hp,hcsp.HCSP):
                    P.append(PureAssertion(p,rec(hp.else_hp,remain)))
                return OpAssn_mult("||",P)
        elif isinstance(hp, hcsp.Assign):
            return remain.substVar(hp.var_name.name, expr_to_eexpr(hp.expr))
        elif isinstance(hp, hcsp.InputChannel):
            dname, vname = variant_name(bound_vars, "d"), variant_name(bound_vars, "v")
            return WaitInAssertion(id_inv, hp.ch_name.name,
                               ParamAssertion([dname, vname],
                                              remain.substVar(hp.var_name.name, VarExpr(vname))))
        elif isinstance(hp, hcsp.OutputChannel):
            dname = variant_name(bound_vars, "d")
            return WaitOutvAssertion(id_inv, hp.ch_name.name, expr_to_eexpr(hp.expr),
                                 ParamAssertion([dname], remain))
        elif isinstance(hp, hcsp.Wait):
            dname = variant_name(bound_vars, "d")
            return WaitAssertion(id_inv, expr_to_eexpr(hp.delay), ParamAssertion([dname], remain))
        elif isinstance(hp, hcsp.ODE_Comm):
            if hp.unsols == []:
                time_var = variant_name(bound_vars, "t")
                solution_dict = solveODE(hp, set(bound_vars), time_var)
                # print(solution_dict)
                inv = id_inv
                # vlist = []
                varlist = []
                exprlist = []
                exprlistt = []
                dname, vname = variant_name(bound_vars, "d"), variant_name(bound_vars, "v")
                ddic = dict()
                ddict = dict()
                ddic[time_var] = expr.AVar(dname)
                ddict[time_var] = expr.AVar("t")
                P = remain
                for fun_name, sol in solution_dict.items():
                    # print(sol)
                    # inv = inv.substVar(fun_name,expr_to_eexpr(sol))
                    # vlist.append(str(fun_name))
                    varlist.append(fun_name)
                    exprlist.append(expr_to_eexpr(sol.subst(ddic)))
                    exprlistt.append(expr_to_eexpr(sol.subst(ddict)))
                    # P = P.substVar(fun_name,expr_to_eexpr(sol.subst(ddic)))
                # vlist.append(time_var)
                inv = inv.substVars(varlist,exprlistt)
                P = P.substVars(varlist,exprlist)

                
                
                comm_specs = []
                for comm_hp, out_hp in hp.io_comms:
                    Q = rec(out_hp,remain)       
                    if comm_hp.type == "input_channel":
                        Q = Q.substVar(comm_hp.var_name.name, VarExpr(vname))
                        Q = Q.substVars(varlist,exprlist)
                        comm_specs.append((Ininf(comm_hp.ch_name.name),ParamAssertion([dname, vname],Q)))
                    else:
                        Q = Q.substVars(varlist,exprlist)
                        comm_specs.append((Outinf(comm_hp.ch_name.name,expr_to_eexpr(comm_hp.expr).substVars(varlist,exprlist)),ParamAssertion([dname],Q)))
                # for i in comm_specs:
                #         print(i[0])

                cons = hp.constraint.subst(solution_dict)
                if cons == expr.true_expr:
                    return InterruptinfAssertion(inv, comm_specs)
                else:
                    # consall = expr.LogicExpr('&&', hp.constraint, compute_boundary(cons))
                    # consall = expr.LogicExpr('&&', expr.RelExpr('>=', expr.AVar(time_var), expr.AConst(0)), consall)
                    wait1 = compute_boundary(cons)
                    wait2 = expr.LogicExpr("->", expr.LogicExpr("!", hp.constraint), expr.RelExpr('<=', expr.AVar(time_var), expr.AConst(0)))
                    wait3 = expr.LogicExpr("->", hp.constraint, expr.LogicExpr("&&", expr.RelExpr('>', expr.AVar(time_var), expr.AConst(0)), 
                                                                               expr.ForAllExpr("t", expr.LogicExpr("->", expr.LogicExpr("&&",expr.RelExpr('>=', expr.AVar("t"), expr.AConst(0)),
                                                                                                                                   expr.RelExpr('<', expr.AVar("t"), expr.AVar(time_var))),
                                                                                                                                   cons.subst(ddict)))))
                    waite = wl_reduce(expr.LogicExpr("&&",wait1,expr.LogicExpr("&&",wait2,wait3)),[time_var])
                    return PureAssertion(expr_to_eexpr(waite), InterruptAssertion(inv, VarExpr(time_var), ParamAssertion([dname],P), comm_specs))
            
            elif len(hp.unsols)<len(hp.eqs):
                assert not hp.constraint.get_vars() & set(hp.unsols)
                neqs = []
                for t in hp.eqs:
                    if t[0] not in hp.unsols:
                        neqs.append(t)
                nhp = hcsp.ODE(neqs,hp.constraint)
                time_var = variant_name(bound_vars, "t")
                solution_dict = solveODE(nhp, set(bound_vars), time_var)
                # print(solution_dict)
                # inv = id_inv
                # vlist = []
                varlist = []
                exprlist = []
                exprlistt = []
                dname, vname = variant_name(bound_vars, "d"), variant_name(bound_vars, "v")
                ddic = dict()
                ddict = dict()
                ddic[time_var] = expr.AVar(dname)
                ddict[time_var] = expr.AVar("t")
                sols = []
                P = remain
                for fun_name, sol in solution_dict.items():
                    # print(sol)
                    # inv = inv.substVar(fun_name,expr_to_eexpr(sol))
                    # vlist.append(str(fun_name))
                    varlist.append(fun_name)
                    exprlist.append(expr_to_eexpr(sol.subst(ddic)))
                    exprlistt.append(expr_to_eexpr(sol.subst(ddict)))
                    # P = P.substVar(fun_name,expr_to_eexpr(sol.subst(ddic)))

                us_var = variant_name(bound_vars, "us")
                inv = ODEPathInvariant(expr_to_eexpr(hp.inv[0].expr), hp.eqs, (varlist, exprlistt), us_var, expr_to_eexpr(hp.constraint))
                
                
                for vv in hp.unsols:
                    varlist.append(vv)
                    exprlist.append(VarExpr(us_var+vv))

                # vlist.append(time_var)
                P = P.substVars(varlist,exprlist)
                G1 = LogicExpr("->", RelExpr(">", VarExpr(dname), ConstExpr(0)), expr_to_eexpr(hp.inv[0].expr).substVars(varlist,exprlist))
                L = []
                for vv in hp.unsols:
                    L.append(RelExpr("==", VarExpr(vv), VarExpr(us_var+vv)))
                G2 = LogicExpr("->", RelExpr("<=", VarExpr(dname), ConstExpr(0)), LogicExpr_mult("&&", L))
                P = PureAssertion(LogicExpr("&&", G1, G2), P)

                comm_specs = []
                for comm_hp, out_hp in hp.io_comms:
                    Q = rec(out_hp,remain)       
                    if comm_hp.type == "input_channel":
                        Q = Q.substVar(comm_hp.var_name.name, VarExpr(vname))
                        Q = Q.substVars(varlist,exprlist)
                        Q = PureAssertion(LogicExpr("&&", G1, G2), Q)
                        comm_specs.append((Ininf(comm_hp.ch_name.name),ParamAssertion([dname, vname],Q)))
                    else:
                        Q = Q.substVars(varlist,exprlist)
                        Q = PureAssertion(LogicExpr("&&", G1, G2), Q)
                        comm_specs.append((Outinf(comm_hp.ch_name.name,expr_to_eexpr(comm_hp.expr).substVars(varlist,exprlist)),ParamAssertion([dname],Q)))
                # for i in comm_specs:
                #         print(i[0])

                cons = hp.constraint.subst(solution_dict)
                if cons == expr.true_expr:
                    return InterruptinfAssertion(inv, comm_specs)
                else:
                    # consall = expr.LogicExpr('&&', hp.constraint, compute_boundary(cons))
                    # consall = expr.LogicExpr('&&', expr.RelExpr('>=', expr.AVar(time_var), expr.AConst(0)), consall)
                    wait1 = compute_boundary(cons)
                    wait2 = expr.LogicExpr("->", expr.LogicExpr("!", hp.constraint), expr.RelExpr('<=', expr.AVar(time_var), expr.AConst(0)))
                    wait3 = expr.LogicExpr("->", hp.constraint, expr.LogicExpr("&&", expr.RelExpr('>', expr.AVar(time_var), expr.AConst(0)), 
                                                                               expr.ForAllExpr("t", expr.LogicExpr("->", expr.LogicExpr("&&",expr.RelExpr('>=', expr.AVar("t"), expr.AConst(0)),
                                                                                                                                   expr.RelExpr('<', expr.AVar("t"), expr.AVar(time_var))),
                                                                                                                                   cons.subst(ddict)))))
                    waite = wl_reduce(expr.LogicExpr("&&",wait1,expr.LogicExpr("&&",wait2,wait3)),[time_var])
                    return PureAssertion(expr_to_eexpr(waite), InterruptAssertion(inv, VarExpr(time_var), ParamAssertion([dname],P), comm_specs))
            
            else:
                raise NotImplementedError


        elif isinstance(hp, hcsp.ODE_Commn):
            if hp.unsols == []:
                time_var = variant_name(bound_vars, "t")
                solution_dict = solveODE(hp, set(bound_vars), time_var)
                # print(solution_dict)
                inv = id_inv
                # vlist = []
                varlist = []
                exprlist = []
                exprlistt = []
                dname, vname = variant_name(bound_vars, "d"), variant_name(bound_vars, "v")
                ddic = dict()
                ddict = dict()
                ddic[time_var] = expr.AVar(dname)
                ddict[time_var] = expr.AVar("t")
                P = rec(hp.tail, remain)
                for fun_name, sol in solution_dict.items():
                    # print(sol)
                    # inv = inv.substVar(fun_name,expr_to_eexpr(sol))
                    # vlist.append(str(fun_name))
                    varlist.append(fun_name)
                    exprlist.append(expr_to_eexpr(sol.subst(ddic)))
                    exprlistt.append(expr_to_eexpr(sol.subst(ddict)))
                    # P = P.substVar(fun_name,expr_to_eexpr(sol.subst(ddic)))
                # vlist.append(time_var)
                inv = inv.substVars(varlist,exprlistt)
                P = P.substVars(varlist,exprlist)

                
                
                comm_specs = []
                for comm_hp, out_hp in hp.io_comms:
                    Q = rec(out_hp,remain)       
                    if comm_hp.type == "input_channel":
                        Q = Q.substVar(comm_hp.var_name.name, VarExpr(vname))
                        Q = Q.substVars(varlist,exprlist)
                        comm_specs.append((Ininf(comm_hp.ch_name.name),ParamAssertion([dname, vname],Q)))
                    else:
                        Q = Q.substVars(varlist,exprlist)
                        comm_specs.append((Outinf(comm_hp.ch_name.name,expr_to_eexpr(comm_hp.expr).substVars(varlist,exprlist)),ParamAssertion([dname],Q)))
                # for i in comm_specs:
                #         print(i[0])

                cons = hp.constraint.subst(solution_dict)
                if cons == expr.true_expr:
                    return InterruptinfAssertion(inv, comm_specs)
                else:
                    # consall = expr.LogicExpr('&&', hp.constraint, compute_boundary(cons))
                    # consall = expr.LogicExpr('&&', expr.RelExpr('>=', expr.AVar(time_var), expr.AConst(0)), consall)
                    wait1 = compute_boundary(cons)
                    wait2 = expr.LogicExpr("->", expr.LogicExpr("!", hp.constraint), expr.RelExpr('<=', expr.AVar(time_var), expr.AConst(0)))
                    wait3 = expr.LogicExpr("->", hp.constraint, expr.LogicExpr("&&", expr.RelExpr('>', expr.AVar(time_var), expr.AConst(0)), 
                                                                               expr.ForAllExpr("t", expr.LogicExpr("->", expr.LogicExpr("&&",expr.RelExpr('>=', expr.AVar("t"), expr.AConst(0)),
                                                                                                                                   expr.RelExpr('<', expr.AVar("t"), expr.AVar(time_var))),
                                                                                                                                   cons.subst(ddict)))))
                    waite = wl_reduce(expr.LogicExpr("&&",wait1,expr.LogicExpr("&&",wait2,wait3)),[time_var])
                    return PureAssertion(expr_to_eexpr(waite), InterruptAssertion(inv, VarExpr(time_var), ParamAssertion([dname],P), comm_specs))
            
            elif len(hp.unsols)<len(hp.eqs):
                assert not hp.constraint.get_vars() & set(hp.unsols)
                neqs = []
                for t in hp.eqs:
                    if t[0] not in hp.unsols:
                        neqs.append(t)
                nhp = hcsp.ODE(neqs,hp.constraint)
                time_var = variant_name(bound_vars, "t")
                solution_dict = solveODE(nhp, set(bound_vars), time_var)
                # print(solution_dict)
                # inv = id_inv
                # vlist = []
                varlist = []
                exprlist = []
                exprlistt = []
                dname, vname = variant_name(bound_vars, "d"), variant_name(bound_vars, "v")
                ddic = dict()
                ddict = dict()
                ddic[time_var] = expr.AVar(dname)
                ddict[time_var] = expr.AVar("t")
                sols = []
                P = rec(hp.tail, remain)
                for fun_name, sol in solution_dict.items():
                    # print(sol)
                    # inv = inv.substVar(fun_name,expr_to_eexpr(sol))
                    # vlist.append(str(fun_name))
                    varlist.append(fun_name)
                    exprlist.append(expr_to_eexpr(sol.subst(ddic)))
                    exprlistt.append(expr_to_eexpr(sol.subst(ddict)))
                    # P = P.substVar(fun_name,expr_to_eexpr(sol.subst(ddic)))

                us_var = variant_name(bound_vars, "us")
                inv = ODEPathInvariant(expr_to_eexpr(hp.inv[0].expr), hp.eqs, (varlist, exprlistt), us_var, expr_to_eexpr(hp.constraint))
                
                for vv in hp.unsols:
                    varlist.append(vv)
                    exprlist.append(VarExpr(us_var+vv))

                # vlist.append(time_var)
                
                P = P.substVars(varlist,exprlist)
                G1 = LogicExpr("->", RelExpr(">", VarExpr(dname), ConstExpr(0)), expr_to_eexpr(hp.inv[0].expr).substVars(varlist,exprlist))
                L = []
                for vv in hp.unsols:
                    L.append(RelExpr("==", VarExpr(vv), VarExpr(us_var+vv)))
                G2 = LogicExpr("->", RelExpr("<=", VarExpr(dname), ConstExpr(0)), LogicExpr_mult("&&", L))
                P = PureAssertion(LogicExpr("&&", G1, G2), P)

                comm_specs = []
                for comm_hp, out_hp in hp.io_comms:
                    Q = rec(out_hp,remain)       
                    if comm_hp.type == "input_channel":
                        Q = Q.substVar(comm_hp.var_name.name, VarExpr(vname))
                        Q = Q.substVars(varlist,exprlist)
                        Q = PureAssertion(LogicExpr("&&", G1, G2), Q)
                        comm_specs.append((Ininf(comm_hp.ch_name.name),ParamAssertion([dname, vname],Q)))
                    else:
                        Q = Q.substVars(varlist,exprlist)
                        Q = PureAssertion(LogicExpr("&&", G1, G2), Q)
                        comm_specs.append((Outinf(comm_hp.ch_name.name,expr_to_eexpr(comm_hp.expr).substVars(varlist,exprlist)),ParamAssertion([dname],Q)))
                # for i in comm_specs:
                #         print(i[0])

                cons = hp.constraint.subst(solution_dict)
                if cons == expr.true_expr:
                    return InterruptinfAssertion(inv, comm_specs)
                else:
                    # consall = expr.LogicExpr('&&', hp.constraint, compute_boundary(cons))
                    # consall = expr.LogicExpr('&&', expr.RelExpr('>=', expr.AVar(time_var), expr.AConst(0)), consall)
                    wait1 = compute_boundary(cons)
                    wait2 = expr.LogicExpr("->", expr.LogicExpr("!", hp.constraint), expr.RelExpr('<=', expr.AVar(time_var), expr.AConst(0)))
                    wait3 = expr.LogicExpr("->", hp.constraint, expr.LogicExpr("&&", expr.RelExpr('>', expr.AVar(time_var), expr.AConst(0)), 
                                                                               expr.ForAllExpr("t", expr.LogicExpr("->", expr.LogicExpr("&&",expr.RelExpr('>=', expr.AVar("t"), expr.AConst(0)),
                                                                                                                                   expr.RelExpr('<', expr.AVar("t"), expr.AVar(time_var))),
                                                                                                                                   cons.subst(ddict)))))
                    waite = wl_reduce(expr.LogicExpr("&&",wait1,expr.LogicExpr("&&",wait2,wait3)),[time_var])
                    return PureAssertion(expr_to_eexpr(waite), InterruptAssertion(inv, VarExpr(time_var), ParamAssertion([dname],P), comm_specs))
            
            else:
                raise NotImplementedError
            
        elif isinstance(hp, hcsp.ODE):
            if hp.unsols == []:
                time_var = variant_name(bound_vars, "t")
                solution_dict = solveODE(hp, set(bound_vars), time_var)
                # print(solution_dict)
                inv = id_inv
                # vlist = []
                varlist = []
                exprlist = []
                exprlistt = []
                dname= variant_name(bound_vars, "d")
                ddic = dict()
                ddict = dict()
                ddic[time_var] = expr.AVar(dname)
                ddict[time_var] = expr.AVar("t")
                P = remain
                for fun_name, sol in solution_dict.items():
                    # print(sol)
                    # inv = inv.substVar(fun_name,expr_to_eexpr(sol))
                    # vlist.append(str(fun_name))
                    varlist.append(fun_name)
                    exprlist.append(expr_to_eexpr(sol.subst(ddic)))
                    exprlistt.append(expr_to_eexpr(sol.subst(ddict)))
                    # P = P.substVar(fun_name,expr_to_eexpr(sol.subst(ddic)))
                # vlist.append(time_var)
                P = P.substVars(varlist,exprlist)
                inv = inv.substVars(varlist,exprlistt)
                

                cons = hp.constraint.subst(solution_dict)
                if cons == expr.true_expr:
                    raise NotImplementedError
                else:
                    # consall = expr.LogicExpr('&&', hp.constraint, compute_boundary(cons))
                    # consall = expr.LogicExpr('&&', expr.RelExpr('>=', expr.AVar(time_var), expr.AConst(0)), consall)
                    wait1 = compute_boundary(cons)
                    wait2 = expr.LogicExpr("->", expr.LogicExpr("!", hp.constraint), expr.RelExpr('<=', expr.AVar(time_var), expr.AConst(0)))
                    wait3 = expr.LogicExpr("->", hp.constraint, expr.LogicExpr("&&", expr.RelExpr('>', expr.AVar(time_var), expr.AConst(0)), 
                                                                               expr.ForAllExpr("t", expr.LogicExpr("->", expr.LogicExpr("&&",expr.RelExpr('>=', expr.AVar("t"), expr.AConst(0)),
                                                                                                                                   expr.RelExpr('<', expr.AVar("t"), expr.AVar(time_var))),
                                                                                                                                   cons.subst(ddict)))))
                    waite = wl_reduce(expr.LogicExpr("&&",wait1,expr.LogicExpr("&&",wait2,wait3)),[time_var])
                    return PureAssertion(expr_to_eexpr(waite), WaitAssertion(inv, VarExpr(time_var), ParamAssertion([dname],P)))
                
            elif len(hp.unsols)<len(hp.eqs):
                assert not hp.constraint.get_vars() & set(hp.unsols)
                neqs = []
                for t in hp.eqs:
                    if t[0] not in hp.unsols:
                        neqs.append(t)
                nhp = hcsp.ODE(neqs,hp.constraint)
                time_var = variant_name(bound_vars, "t")
                solution_dict = solveODE(nhp, set(bound_vars), time_var)
                # print(solution_dict)
                # inv = id_inv
                # vlist = []
                varlist = []
                exprlist = []
                exprlistt = []
                dname= variant_name(bound_vars, "d")
                ddic = dict()
                ddict = dict()
                ddic[time_var] = expr.AVar(dname)
                ddict[time_var] = expr.AVar("t")
                sols = []
                P = remain
                for fun_name, sol in solution_dict.items():
                    # print(sol)
                    # inv = inv.substVar(fun_name,expr_to_eexpr(sol))
                    # vlist.append(str(fun_name))
                    varlist.append(fun_name)
                    exprlist.append(expr_to_eexpr(sol.subst(ddic)))
                    exprlistt.append(expr_to_eexpr(sol.subst(ddict)))
                    # P = P.substVar(fun_name,expr_to_eexpr(sol.subst(ddic)))

                us_var = variant_name(bound_vars, "us")
                inv = ODEPathInvariant(expr_to_eexpr(hp.inv[0].expr), hp.eqs, (varlist, exprlistt), us_var, expr_to_eexpr(hp.constraint))

                for vv in hp.unsols:
                    varlist.append(vv)
                    exprlist.append(VarExpr(us_var+vv))
                # print(inv.sols)
                # vlist.append(time_var)
                
                P = P.substVars(varlist,exprlist)

                G1 = LogicExpr("->", RelExpr(">", VarExpr(dname), ConstExpr(0)), expr_to_eexpr(hp.inv[0].expr).substVars(varlist,exprlist))
                L = []
                for vv in hp.unsols:
                    L.append(RelExpr("==", VarExpr(vv), VarExpr(us_var+vv)))
                G2 = LogicExpr("->", RelExpr("<=", VarExpr(dname), ConstExpr(0)), LogicExpr_mult("&&", L))
                P = PureAssertion(LogicExpr("&&", G1, G2), P)

                cons = hp.constraint.subst(solution_dict)
                if cons == expr.true_expr:
                    raise NotImplementedError
                else:
                    # consall = expr.LogicExpr('&&', hp.constraint, compute_boundary(cons))
                    # consall = expr.LogicExpr('&&', expr.RelExpr('>=', expr.AVar(time_var), expr.AConst(0)), consall)
                    wait1 = compute_boundary(cons)
                    wait2 = expr.LogicExpr("->", expr.LogicExpr("!", hp.constraint), expr.RelExpr('<=', expr.AVar(time_var), expr.AConst(0)))
                    wait3 = expr.LogicExpr("->", hp.constraint, expr.LogicExpr("&&", expr.RelExpr('>', expr.AVar(time_var), expr.AConst(0)), 
                                                                               expr.ForAllExpr("t", expr.LogicExpr("->", expr.LogicExpr("&&",expr.RelExpr('>=', expr.AVar("t"), expr.AConst(0)),
                                                                                                                                   expr.RelExpr('<', expr.AVar("t"), expr.AVar(time_var))),
                                                                                                                                   cons.subst(ddict)))))
                    waite = wl_reduce(expr.LogicExpr("&&",wait1,expr.LogicExpr("&&",wait2,wait3)),[time_var])
                    return PureAssertion(expr_to_eexpr(waite), WaitAssertion(inv, VarExpr(time_var), ParamAssertion([dname],P)))
                
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    return rec(hp, init)

def add_pn_var(pn:str, v: str, l = []) -> str:
    if v in l:
        return v
    else:
        return pn+v
    


def add_pn_eexpr(pn:str, e: EExpr, l = []) -> EExpr:
    if isinstance(e, BoundVar):
        return BoundVar(add_pn_var(pn,e.name,l))
    elif isinstance(e, VarExpr):
        return VarExpr(add_pn_var(pn,e.name,l))
    elif isinstance(e, ConstExpr):
        return e
    elif isinstance(e, BConstExpr):
        return e
    elif isinstance(e, VarSubstExpr):
        return VarSubstExpr(add_pn_eexpr(pn,e.start_expr,l), add_pn_var(pn,e.var,l), add_pn_eexpr(pn,e.expr,l))
    elif isinstance(e, VarsSubstExpr):
        vars = [add_pn_var(pn,var,l) for var in e.vars]
        exprs = [add_pn_eexpr(pn,expr,l) for expr in e.exprs]
        return VarsSubstExpr(add_pn_eexpr(pn,e.start_expr,l), vars, exprs)
    elif isinstance(e, OpExpr):
        return OpExpr(e.op, *(add_pn_eexpr(pn,sube,l) for sube in e.exprs))
    elif isinstance(e, LogicExpr):
        return LogicExpr(e.op, *(add_pn_eexpr(pn,sube,l) for sube in e.exprs))
    elif isinstance(e, RelExpr):
        return RelExpr(e.op, add_pn_eexpr(pn,e.expr1,l), add_pn_eexpr(pn,e.expr2,l))
    elif isinstance(e, IfExpr):
        return IfExpr(add_pn_eexpr(pn,e.cond,l), add_pn_eexpr(pn,e.if_branch,l), add_pn_eexpr(pn,e.else_branch,l))
    elif isinstance(e, ExistsExpr):
        return ExistsExpr([add_pn_var(pn,var,l) for var in e.bound_names], add_pn_eexpr(pn,e.expr,l))
    else:
        raise NotImplementedError
    
def add_0_eexpr(e: EExpr, l = []) -> EExpr:
    if isinstance(e, VarExpr):
        if e.name in l:
            return e
        else:
            return VarExpr(e.name+"00")
    elif isinstance(e, ConstExpr):
        return e
    elif isinstance(e, BConstExpr):
        return e
    elif isinstance(e, OpExpr):
        return OpExpr(e.op, *(add_0_eexpr(sube,l) for sube in e.exprs))
    elif isinstance(e, LogicExpr):
        return LogicExpr(e.op, *(add_0_eexpr(sube,l) for sube in e.exprs))
    elif isinstance(e, RelExpr):
        return RelExpr(e.op, add_0_eexpr(e.expr1,l), add_0_eexpr(e.expr2,l))
    elif isinstance(e, IfExpr):
        return IfExpr(add_0_eexpr(e.cond,l), add_0_eexpr(e.if_branch,l), add_0_eexpr(e.else_branch,l))
    else:
        print(e)
        raise NotImplementedError



def add_pn_path(pn:str, P:PathInvariant) -> PathInvariant:
    if isinstance(P, IdPathInvariant):
        return id_inv
    elif isinstance(P, ExprPathInvariant):
        return ExprPathInvariant(add_pn_eexpr(pn,P.expr,["t"]))
    elif isinstance(P,SubstVarPathInvariant):
        return SubstVarPathInvariant(add_pn_path(pn,P.start_path_inv),add_pn_var(pn,P.var,["t"]),add_pn_eexpr(pn,P.expr,["t"]))
    elif isinstance(P,SubstVarsPathInvariant):
        vars = [add_pn_var(pn,var,["t"]) for var in P.vars]
        exprs = [add_pn_eexpr(pn,expr,["t"]) for expr in P.exprs]
        return SubstVarsPathInvariant(add_pn_path(pn,P.start_path_inv),vars,exprs)
    elif isinstance(P,ODEPathInvariant):
        assert P.pn is None
        vars = [add_pn_var(pn,var,["t"]) for var in P.sols[0]]
        exprs = [add_pn_eexpr(pn,expr,["t"]) for expr in P.sols[1]]
        return ODEPathInvariant(add_pn_eexpr(pn,P.expr,["t"]), P.eqs, (vars,exprs), add_pn_var(pn,P.unsol,["t"]), P.cons, pn)
    else:
        raise NotImplementedError
    
def add_pn_assn(pn:str, A:Assertion, BL=[]) -> Assertion:
    if isinstance(A,FalseAssertion):
        return Fassn
    
    elif isinstance(A,InitAssertion):
        return init
    
    elif isinstance(A,WaitInAssertion):
        return WaitInAssertion(add_pn_path(pn,A.path_inv),A.ch_name,add_pn_assn(pn,A.param_assn,BL))
    
    elif isinstance(A,WaitOutvAssertion):
        return WaitOutvAssertion(add_pn_path(pn,A.path_inv),A.ch_name,add_0_eexpr(add_pn_eexpr(pn,A.expr),BL),add_pn_assn(pn,A.param_assn,BL))
    
    elif isinstance(A,ParamAssertion):
        names = [add_pn_var(pn,name) for name in A.bound_names]
        nBL = BL + names
        return ParamAssertion(names,add_pn_assn(pn,A.assn,nBL))
    
    elif isinstance(A,VarSubstAssertion):
        return VarSubstAssertion(add_pn_assn(pn,A.start_assn,BL),add_pn_var(pn,A.var),add_pn_eexpr(pn,A.expr))
    
    elif isinstance(A,VarsSubstAssertion):
        vars = [add_pn_var(pn,var) for var in A.vars]
        exprs = [add_pn_eexpr(pn,expr) for expr in A.exprs]
        return VarsSubstAssertion(add_pn_assn(pn,A.start_assn,BL),vars,exprs)
    
    elif isinstance(A,RecAssertion):
        return RecAssertion(add_pn_var(pn,A.rec_var),add_pn_assn(pn,A.assn,BL))
    
    elif isinstance(A,RecursionVar):
        return RecursionVar(add_pn_var(pn,A.name))
    
    elif isinstance(A,OpAssn):
        return OpAssn(A.op, *(add_pn_assn(pn,assn,BL) for assn in A.assns))
    
    elif isinstance(A,PureAssertion):
        return PureAssertion(add_pn_eexpr(pn,A.expr), add_pn_assn(pn,A.assn,BL))
    
    elif isinstance(A,WaitAssertion):
        return WaitAssertion(add_pn_path(pn,A.path_inv), add_pn_eexpr(pn,A.delay_expr),add_pn_assn(pn,A.param_assn,BL))
    
    elif isinstance(A,InterruptAssertion):
        comm_specs = []
        for i in A.comm_specs:
            if isinstance(i[0],Ininf):
                comm_specs.append((Ininf(i[0].ch_name),add_pn_assn(pn,i[1],BL)))
            elif isinstance(i[0],Outinf):
                nBL = [add_pn_var(pn,name) for name in i[1].bound_names]
                comm_specs.append((Outinf(i[0].ch_name,add_0_eexpr(add_pn_eexpr(pn,i[0].expr),BL+nBL)),add_pn_assn(pn,i[1],BL)))
            else :
                raise NotImplementedError
        return InterruptAssertion(add_pn_path(pn,A.path_inv), add_pn_eexpr(pn,A.delay_expr), add_pn_assn(pn,A.param_assn,BL), comm_specs)
    
    elif isinstance(A,InterruptinfAssertion):
        comm_specs = []
        for i in A.comm_specs:
            if isinstance(i[0],Ininf):
                comm_specs.append((Ininf(i[0].ch_name),add_pn_assn(pn,i[1],BL)))
            elif isinstance(i[0],Outinf):
                nBL = [add_pn_var(pn,name) for name in i[1].bound_names]
                comm_specs.append((Outinf(i[0].ch_name,add_0_eexpr(add_pn_eexpr(pn,i[0].expr),BL+nBL)),add_pn_assn(pn,i[1],BL)))
            else :
                raise NotImplementedError
        return InterruptinfAssertion(add_pn_path(pn,A.path_inv), comm_specs)
    else:
        raise NotImplementedError

def compat_rdy(comm1,comm2):
    pair = []
    for i in comm1:
        for j in comm2:
            if isinstance(i[0],Ininf) and isinstance(j[0],Outinf) and i[0].ch_name == j[0].ch_name:
                pair.append((i,j))
            if isinstance(i[0],Outinf) and isinstance(j[0],Ininf) and i[0].ch_name == j[0].ch_name:
                pair.append((i,j))
    return pair

def OpAssnOr(assn1,assn2):
    if assn1 == Fassn:
        return assn2
    elif assn2 == Fassn:
        return assn1
    else:
        return OpAssn("||",assn1,assn2)
    
def OpAssnOr_mult(assn_list):
    if len(assn_list)==0:
        raise NotImplementedError
    elif len(assn_list)==1:
        return assn_list[0]
    else:
        return OpAssnOr(assn_list[0],OpAssnOr_mult(assn_list[1:]))
    

def verify_ode(hp: hcsp.ODE):

    def constraint_examination(e):
        '''Examine whether the constraint is open intervals or not.'''
        if not isinstance(e, expr.Expr):
            raise NotImplementedError
        
        def rec(e):
            if e == expr.true_expr:
                return True
            elif isinstance(e, expr.RelExpr):
                if e.op in [">", "<", "!="]:
                    return True
                else:
                    return False
            elif isinstance(e, expr.LogicExpr):
                if e.op == '!':
                    return not rec(e.exprs[0])
                elif e.op == '&&' or e.op == '||':
                    return rec(e.exprs[0] and e.exprs[1])
        return rec(e)
    
    constraint = hp.constraint

    if not constraint_examination(constraint):
        raise AssertionError("Constriant is supposed to be open intervals!")

    eqs_dict = {}

    for name, deriv in hp.eqs:
        eqs_dict[name] = deriv
    ghost_vars = []

    if hp.inv is None:
        hp.inv = (assertion.CutInvariant(expr=expr.true_expr, proof_methods=None),)

    assert all(isinstance(inv, assertion.CutInvariant) for inv in hp.inv)
    inv_exprs = [inv.expr for inv in hp.inv]
    inv_cond = expr.conj(*inv_exprs)

    
    if hp.ghosts:
        for ghost in hp.ghosts:
            ghost_var_degree = degree(sympify(str(ghost.diff).replace('^', '**')), gen=symbols(ghost.var))
            if not ghost_var_degree in {0,1}:
                raise AssertionError("Ghost equations should be linear in ghost variable!")
            eqs_dict[ghost.var] = ghost.diff
            ghost_vars.append(ghost.var)
        inv_cond = expr.ExistsExpr(ghost_vars, inv_cond)
    
    closureD = compute_closure(constraint)
    C = closureD

    for i, inv in enumerate(hp.inv):
        if inv.rule is None and inv.expr == expr.true_expr:
            assert inv.rule_arg is None
        
        elif inv.rule == "di" or \
        (inv.rule is None and inv.expr not in (expr.true_expr, expr.false_expr)):
            assert inv.rule_arg is None
            differential = compute_diff(inv.expr, eqs_dict, dict())
            if wl_prove(expr.imp(C,differential)):
                C = expr.LogicExpr("&&",C, inv.expr)
            else:
                print("The failed verification condition is :\n",str(expr.imp(C,differential)))
                raise NotImplementedError
        
        elif inv.rule == "dbx":
            dbx_inv = inv.expr
            if isinstance(dbx_inv, expr.LogicExpr): 
                dbx_inv = wl_simplify(dbx_inv)
            assert isinstance(dbx_inv, expr.RelExpr) and \
                dbx_inv.op in {'==', '>', '>=', '<', '<='}, \
                print("The wrong type of %s is %s" %(dbx_inv, type(dbx_inv)))

            if dbx_inv.op == '<':
                dbx_inv = expr.RelExpr('>', dbx_inv.expr2, dbx_inv.expr1)
            elif dbx_inv.op == '<=':
                dbx_inv = expr.RelExpr('>=', dbx_inv.expr2, dbx_inv.expr1)
            if dbx_inv.expr2 != expr.AConst(0):
                expr1 =  expr.OpExpr('-', dbx_inv.expr1, dbx_inv.expr2)
                expr1 = wl_simplify(expr1)
                dbx_inv = expr.RelExpr(dbx_inv.op, expr1, expr.AConst(0)) 
            
            e = dbx_inv.expr1
            assert wl_is_polynomial(e) is True
            e_lie_deriv = compute_diff(e, eqs_dict, dict())             

            if dbx_inv.op == "==" :

                if inv.rule_arg is None:
                    g = expr.OpExpr('/', e_lie_deriv, e)
                    g = wl_simplify(g)
                    assert wl_is_polynomial(g) is True

                else:
                    g = inv.rule_arg
                    assert wl_is_polynomial(g) is True
                    vc = expr.imp(C, expr.RelExpr('==', e_lie_deriv, 
                                                                expr.OpExpr('*', g, e)))

            elif dbx_inv.op in {'>', '>='}:
                if inv.rule_arg is None:
                    quot_remains = wl_polynomial_div(e_lie_deriv, e, set())
                    
                    vc_comps = []
                    for _, remain in quot_remains.items():
                        vc_comp = expr.RelExpr('>=', remain, expr.AConst(0))
                        vc_comps.append(vc_comp)
                    vc = expr.imp(C, expr.list_disj(*vc_comps))

                else:
                    g = inv.rule_arg
                    assert wl_is_polynomial(g) is True
                    
                    vc = expr.imp(C, expr.RelExpr('>=', e_lie_deriv, 
                                                                expr.OpExpr('*', g, e)))
                    
            if wl_prove(vc):
                C = expr.LogicExpr("&&",C, inv.expr)
            else:
                print("The failed verification condition is :\n",str(vc))
                raise NotImplementedError
            
        elif inv.rule == "bc":
            assert inv.rule_arg is None

            barrier_inv = inv.expr
        
            if isinstance(barrier_inv, expr.LogicExpr):
                barrier_inv = wl_simplify(barrier_inv)

            assert isinstance(barrier_inv, expr.RelExpr) and \
                barrier_inv.op in {'<=', '>=', '>', '<'}

            if barrier_inv.op == '<=':
                barrier_inv = expr.RelExpr('>=', barrier_inv.expr2, barrier_inv.expr1)
            elif barrier_inv.op == '<':
                barrier_inv = expr.RelExpr('>', barrier_inv.expr2, barrier_inv.expr1)

            if barrier_inv.expr2 != 0:
                expr1 = expr.OpExpr('-', barrier_inv.expr1, barrier_inv.expr2)
                barrier_inv = expr.RelExpr(barrier_inv.op, expr1, expr.AConst(0))

            e = barrier_inv.expr1
            e_lie = compute_diff(e, eqs_dict, dict())

            vc = expr.imp(expr.LogicExpr('&&', C, 
                                            expr.RelExpr('==', e, expr.AConst(0))),
                        expr.RelExpr('>', e_lie, expr.AConst(0)))
            if wl_prove(vc):
                C = expr.LogicExpr("&&",C, inv.expr)
            else:
                print("The failed verification condition is :\n",str(vc))
                raise NotImplementedError
            
        
        else:
            if inv.rule is not None:
                raise NotImplementedError("Unknown ODE method")
            
    return expr_to_eexpr(inv_cond), expr_to_eexpr(C)


def entails(cond:EExpr, A1:Assertion, A2:Assertion):
    if isinstance(A1, InitAssertion) and isinstance(A2, InitAssertion):
        return True
    elif isinstance(A1, TrueAssertion) and isinstance(A2, TrueAssertion):
        return True
    elif isinstance(A1, FalseAssertion) and isinstance(A2, FalseAssertion):
        return True
    elif isinstance(A2, OpAssn) and A2.op== "||":
        return entails(cond, A1, A2.assns[0]) or entails(cond, A1, A2.assns[1])
    elif isinstance(A2, PureAssertion):
        return wl_prove(eexpr_to_expr(LogicExpr("->", cond, A2.expr))) and entails(cond, A1, A2.assn)
    elif isinstance(A1, VarSubstAssertion) and isinstance(A2, VarSubstAssertion):
        if entails(cond, A1.start_assn, A2.start_assn) and A1.var == A2.var and eexpr_to_expr(A1.expr)==eexpr_to_expr(A2.expr):
            return True
        else:
            return False
    elif isinstance(A1, VarsSubstAssertion) and isinstance(A2, VarsSubstAssertion):
        if entails(cond, A1.start_assn, A2.start_assn) and len(A1.vars) == len(A2.vars) and all(A1.vars[i] ==  A2.vars[i] for i in range(len(A1.vars)))  and all(eexpr_to_expr(A1.exprs[i])==eexpr_to_expr(A2.exprs[i]) for i in range(len(A1.exprs))):
            return True
        else:
            return False
    elif isinstance(A1, ParamAssertion) and isinstance(A2, ParamAssertion):
        return A1.bound_names == A2.bound_names and entails(cond, A1.assn, A2.assn)
    else:
        return False


def sync_mult(T) -> Assertion:
    bound_vars = []
    rec_tup = []
    rec_tup_sol = []
    rec_tup_inv = []

    def sync(chset, A1:Assertion, A2:Assertion, cond:EExpr=BConstExpr(bool(1))) -> Assertion:
        nonlocal bound_vars
        nonlocal rec_tup
        nonlocal rec_tup_sol
        nonlocal rec_tup_inv
        # print(cond)

        if isinstance(A1,FalseAssertion) or isinstance(A2,FalseAssertion):
            return Fassn
    
        elif isinstance(A1,InitAssertion) and isinstance(A2,InitAssertion):
            return init

        elif isinstance(A1,VarSubstAssertion):
            varname = variant_name(bound_vars, A1.var)
            condd = ExistsExpr([varname],LogicExpr("&&",cond.substVar(A1.var,VarExpr(varname)),RelExpr("==",VarExpr(A1.var),A1.expr.substVar(A1.var,VarExpr(varname)))))
            # print(condd)
            # print(eexpr_to_expr(condd))
            return sync(chset, A1.start_assn, A2,condd).substVar(A1.var,A1.expr)
    
        elif isinstance(A2,VarSubstAssertion):
            varname = variant_name(bound_vars, A2.var)
            condd = ExistsExpr([varname],LogicExpr("&&",cond.substVar(A2.var,VarExpr(varname)),RelExpr("==",VarExpr(A2.var),A2.expr.substVar(A2.var,VarExpr(varname)))))
            return sync(chset, A1, A2.start_assn,condd).substVar(A2.var,A2.expr)
        
        elif isinstance(A1,VarsSubstAssertion):
            varnames = []
            varexprs = []
            for var in A1.vars:
                varname = variant_name(bound_vars, var)
                varnames.append(varname)
                varexprs.append(VarExpr(varname))
            condd = cond.substVars(A1.vars,varexprs)
            for i in range(0,len(A1.vars)):
                condd = LogicExpr("&&",condd,RelExpr("==",VarExpr(A1.vars[i]),A1.exprs[i].substVars(A1.vars,varexprs)))
            # print(varnames)
            condd = ExistsExpr(varnames,condd)
            # print(condd)
            # print(wl_reduce(eexpr_to_expr(condd),[]))
            return sync(chset, A1.start_assn, A2, condd).substVars(A1.vars,A1.exprs)
    
        elif isinstance(A2,VarsSubstAssertion):
            varnames = []
            varexprs = []
            for var in A2.vars:
                varname = variant_name(bound_vars, var)
                varnames.append(varname)
                varexprs.append(VarExpr(varname))
            condd = cond.substVars(A2.vars,varexprs)
            for i in range(0,len(A2.vars)):
                condd = LogicExpr("&&",condd,RelExpr("==",VarExpr(A2.vars[i]),A2.exprs[i].substVars(A2.vars,varexprs)))
            # print(varnames)
            condd = ExistsExpr(varnames,condd)
            # print(condd)
            # print(wl_reduce(eexpr_to_expr(condd),[]))
            return sync(chset, A1, A2.start_assn,condd).substVars(A2.vars,A2.exprs)
        
        elif isinstance(A1,RecAssertion) and isinstance(A2,RecAssertion):
            for s in rec_tup_sol:
                if s[0].rec_var == A1.rec_var and s[1].rec_var == A2.rec_var:
                    test = LogicExpr("->",cond,s[3])
                    if wl_prove(eexpr_to_expr(test)):
                        return s[4]
                    else:
                        raise NotImplementedError
            Rname = variant_name(bound_vars, "R")
            inv_txt = "true"
            for s in rec_tup_inv:
                if s[0] == A1.rec_var and s[1] == A2.rec_var:
                    inv_txt = s[2]
            inv = expr_to_eexpr(parse_expr_with_meta(inv_txt))
            test = LogicExpr("->",cond,inv)
            # print("suc1")
            # print(eexpr_to_expr(test))
            if wl_prove(eexpr_to_expr(test)):
                # print("suc1")
                rec_tup.append((A1,A2,Rname,inv))
                G = RecAssertion(Rname,sync(chset,A1.assn,A2.assn,inv))
                rec_tup_sol.append((A1,A2,Rname,inv,G))
                return G
            else:
                print("wrong inv")
                raise NotImplementedError
        
        elif isinstance(A1,RecursionVar) and isinstance(A2,RecursionVar):
            for s in rec_tup:
                if s[0].rec_var == A1.name and s[1].rec_var == A2.name:
                    test = test = LogicExpr("->",cond,s[3])
                    # print("suc2")
                    # print(eexpr_to_expr(test))
                    if wl_prove(eexpr_to_expr(test)):
                        # print("suc2")
                        return RecursionVar(s[2])
                    else:
                        print("wrong inv")
                        # print(eexpr_to_expr(test))
                        raise NotImplementedError
        
        elif isinstance(A1,OpAssn):
            if A1.op == "||" and len(A1.assns)==2:
                G1 = sync(chset,A1.assns[0],A2,cond)
                G2 = sync(chset,A1.assns[1],A2,cond)
                return OpAssnOr(G1, G2)
            else:
                raise NotImplementedError
                            
        elif isinstance(A2,OpAssn):
            if A2.op == "||" and len(A2.assns)==2:
                G1 = sync(chset,A1,A2.assns[0],cond)
                G2 = sync(chset,A1,A2.assns[1],cond)
                return OpAssnOr(G1, G2)
            else:
                raise NotImplementedError
            
        elif isinstance(A1,PureAssertion):
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,A1.expr))):
                return Fassn
            else:
                G = sync(chset,A1.assn,A2,LogicExpr("&&",cond,A1.expr))
                if G == Fassn:
                    return Fassn
                else:
                    return PureAssertion(A1.expr,G)
            
        elif isinstance(A2,PureAssertion):
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,A2.expr))):
                return Fassn
            else:
                G = sync(chset,A1,A2.assn,LogicExpr("&&",cond,A2.expr))
                if G == Fassn:
                    return Fassn
                else:
                    return PureAssertion(A2.expr,G)
    
        elif isinstance(A1,WaitInAssertion) and isinstance(A2,InitAssertion):
            if A1.ch_name in chset:
                return Fassn
            else:
                G = sync(chset, A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)), A2, cond)
                if G == Fassn:
                    return Fassn
                else:
                    comm_specs = []
                    param_assn = ParamAssertion(A1.param_assn.bound_names, G)
                    comm_specs.append((Ininf(A1.ch_name),param_assn))
                    return InterruptAssertion(PPathInvariant(A1.path_inv,id_inv), ConstExpr(0), ParamAssertion([A1.param_assn.bound_names[0]],Fassn), comm_specs)

        elif isinstance(A1,WaitOutvAssertion) and isinstance(A2,InitAssertion):
            if A1.ch_name in chset:
                return Fassn
            else:
                G = sync(chset, A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)), A2, cond)
                if G == Fassn:
                    return Fassn
                else:
                    comm_specs = []
                    param_assn = ParamAssertion(A1.param_assn.bound_names, G)
                    comm_specs.append((Outinf(A1.ch_name,A1.expr),param_assn))
                    return InterruptAssertion(PPathInvariant(A1.path_inv,id_inv), ConstExpr(0), ParamAssertion([A1.param_assn.bound_names[0]],Fassn), comm_specs)

        elif isinstance(A1,InitAssertion) and isinstance(A2,WaitInAssertion):
            if A2.ch_name in chset:
                return Fassn
            else:
                G = sync(chset, A1, A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)), cond)
                if G == Fassn:
                    return Fassn
                else:
                    comm_specs = []
                    param_assn = ParamAssertion(A2.param_assn.bound_names, G)
                    comm_specs.append((Ininf(A2.ch_name),param_assn))
                    return InterruptAssertion(PPathInvariant(id_inv,A2.path_inv), ConstExpr(0), ParamAssertion([A2.param_assn.bound_names[0]],Fassn), comm_specs)

        elif isinstance(A1,InitAssertion) and isinstance(A2,WaitOutvAssertion):
            if A2.ch_name in chset:
                return Fassn
            else:
                G = sync(chset, A1, A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)), cond)
                if G == Fassn:
                    return Fassn
                else:
                    comm_specs = []
                    param_assn = ParamAssertion(A2.param_assn.bound_names, G)
                    comm_specs.append((Outinf(A2.ch_name,A2.expr),param_assn))
                    return InterruptAssertion(PPathInvariant(id_inv,A2.path_inv), ConstExpr(0), ParamAssertion([A2.param_assn.bound_names[0]],Fassn), comm_specs)   
             
        elif isinstance(A1,WaitInAssertion) and isinstance(A2,WaitOutvAssertion):
            if A1.ch_name in chset and A2.ch_name in chset:
                if A1.ch_name != A2.ch_name:
                    return Fassn
                else:
                    r1v = A1.param_assn.bound_names[1]
                    r1a = A1.param_assn.assn
                    r2 = A2.param_assn.assn
                    r1 = r1a.substVal(r1v,A2.expr)
                    return sync(chset, r1.substVal(A1.param_assn.bound_names[0],ConstExpr(0)), r2.substVal(A2.param_assn.bound_names[0],ConstExpr(0)), cond)
            elif A1.ch_name in chset and A2.ch_name not in chset:
                G = sync(chset, A1.delay(VarExpr(A2.param_assn.bound_names[0])), A2.param_assn.assn, LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A2.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitOutvAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.ch_name,A2.expr,ParamAssertion(A2.param_assn.bound_names,G))
            elif A1.ch_name not in chset and A2.ch_name in chset:
                G = sync(chset, A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])), LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A1.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitInAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.ch_name,ParamAssertion(A1.param_assn.bound_names,G))
            else:
                a1 = InterruptinfAssertion(A1.path_inv,[(Ininf(A1.ch_name),A1.param_assn)])
                a2 = InterruptinfAssertion(A2.path_inv,[(Outinf(A2.ch_name,A2.expr),A2.param_assn)])
                return sync(chset,a1,a2,cond)
            
        elif isinstance(A1,WaitOutvAssertion) and isinstance(A2,WaitInAssertion):
            if A1.ch_name in chset and A2.ch_name in chset:
                if A1.ch_name != A2.ch_name:
                    return Fassn
                else:
                    r2v = A2.param_assn.bound_names[1]
                    r2a = A2.param_assn.assn
                    r1 = A1.param_assn.assn
                    r2 = r2a.substVal(r2v,A1.expr)
                    return sync(chset, r1.substVal(A1.param_assn.bound_names[0],ConstExpr(0)), r2.substVal(A2.param_assn.bound_names[0],ConstExpr(0)), cond)
            elif A1.ch_name in chset and A2.ch_name not in chset:
                G = sync(chset, A1.delay(VarExpr(A2.param_assn.bound_names[0])), A2.param_assn.assn, LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A2.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitInAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.ch_name,ParamAssertion(A2.param_assn.bound_names,G))
            elif A1.ch_name not in chset and A2.ch_name in chset:
                G = sync(chset, A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])), LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A1.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitOutvAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.ch_name,A1.expr,ParamAssertion(A1.param_assn.bound_names,G))
            else:
                a1 = InterruptinfAssertion(A1.path_inv,[(Outinf(A1.ch_name,A1.expr),A1.param_assn)])
                a2 = InterruptinfAssertion(A2.path_inv,[(Ininf(A2.ch_name),A2.param_assn)])
                return sync(chset,a1,a2,cond)
            
        elif isinstance(A1,WaitInAssertion) and isinstance(A2,WaitInAssertion):
            if A1.ch_name in chset and A2.ch_name in chset:
                return Fassn
            elif A1.ch_name in chset and A2.ch_name not in chset:
                G = sync(chset, A1.delay(VarExpr(A2.param_assn.bound_names[0])), A2.param_assn.assn, LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A2.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitInAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.ch_name,ParamAssertion(A2.param_assn.bound_names,G))
            elif A1.ch_name not in chset and A2.ch_name in chset:
                G = sync(chset, A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])), LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A1.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitInAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.ch_name,ParamAssertion(A1.param_assn.bound_names,G))
            else:
                a1 = InterruptinfAssertion(A1.path_inv,[(Ininf(A1.ch_name),A1.param_assn)])
                a2 = InterruptinfAssertion(A2.path_inv,[(Ininf(A2.ch_name),A2.param_assn)])
                return sync(chset,a1,a2,cond)
            
        elif isinstance(A1,WaitOutvAssertion) and isinstance(A2,WaitOutvAssertion):
            if A1.ch_name in chset and A2.ch_name in chset:
                return Fassn
            elif A1.ch_name in chset and A2.ch_name not in chset:
                G = sync(chset, A1.delay(VarExpr(A2.param_assn.bound_names[0])), A2.param_assn.assn, LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A2.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitOutvAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.ch_name,A2.expr,ParamAssertion(A2.param_assn.bound_names,G))
            elif A1.ch_name not in chset and A2.ch_name in chset:
                G = sync(chset, A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])), LogicExpr("&&",cond,RelExpr("<=",ConstExpr(0),VarExpr(A1.param_assn.bound_names[0]))))
                if G == Fassn:
                    return Fassn
                else:
                    return WaitOutvAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.ch_name,A1.expr,ParamAssertion(A1.param_assn.bound_names,G))
            else:
                a1 = InterruptinfAssertion(A1.path_inv,[(Outinf(A1.ch_name,A1.expr),A1.param_assn)])
                a2 = InterruptinfAssertion(A2.path_inv,[(Outinf(A2.ch_name,A2.expr),A2.param_assn)])
                return sync(chset,a1,a2,cond)
            
        elif isinstance(A1,WaitAssertion) and isinstance(A2,WaitAssertion):
            if wl_prove(eexpr_to_expr(LogicExpr("->",cond,RelExpr(">=",ConstExpr(0),A1.delay_expr)))):
                return sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,cond)
            elif wl_prove(eexpr_to_expr(LogicExpr("->",cond,RelExpr(">=",ConstExpr(0),A2.delay_expr)))):
                return sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),cond)
            else:
                F1 = LogicExpr("&&",RelExpr("<",A1.delay_expr,A2.delay_expr),RelExpr("<",ConstExpr(0),A2.delay_expr))
                F2 = LogicExpr("&&",RelExpr(">",A1.delay_expr,A2.delay_expr),RelExpr("<",ConstExpr(0),A1.delay_expr))
                F3 = LogicExpr("||",RelExpr("==",A1.delay_expr,A2.delay_expr),LogicExpr("&&",RelExpr(">",ConstExpr(0),A1.delay_expr),RelExpr(">",ConstExpr(0),A2.delay_expr)))
    
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                    G1 = Fassn
                else:
                    p1 = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A1.delay_expr),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),ConstExpr(0)))
                                       ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A1.delay_expr),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),A1.delay_expr)))
                    GG1 = sync(chset,A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",F1,p1)))
                    if GG1 == Fassn:
                        G1 = Fassn
                    else:
                        G1 = PureAssertion(F1,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                                            ParamAssertion(A1.param_assn.bound_names,GG1)))
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                    G2 = Fassn
                else:
                    p2 = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),ConstExpr(0)))
                                       ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),A2.delay_expr)))
                    GG2 = sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn,LogicExpr("&&",cond,LogicExpr("&&",F2,p2)))
                    if GG2 == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                                            ParamAssertion(A2.param_assn.bound_names,GG2)))
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F3))):
                    G3 = Fassn
                else:
                    dname = variant_name(bound_vars, "d")
                    p3 = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(dname),ConstExpr(0)))
                                       ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(dname),A2.delay_expr)))
                    GG3 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],VarExpr(dname)),A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],VarExpr(dname)),LogicExpr("&&",cond,LogicExpr("&&",F3,p3)))
                    if GG3 == Fassn:
                        G3 = Fassn
                    else:
                        G3 = PureAssertion(F3,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                                            ParamAssertion([dname],GG3)))
                return OpAssnOr_mult([G1,G2,G3])
        
        elif isinstance(A1,WaitAssertion) and isinstance(A2,WaitInAssertion):
            # if A2.ch_name in chset:
            #     G = WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
            #                          ParamAssertion(A1.param_assn.bound_names,sync(chset,A1.param_assn.assn,
            #                                                                        A2.delay(VarExpr(A1.param_assn.bound_names[0])))))
            # else:
            #     G = InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
            #                               ParamAssertion(A1.param_assn.bound_names,sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])))),
            #                               [(Ininf(A2.ch_name),ParamAssertion(A2.param_assn.bound_names,sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn)))])
            # return OpAssn("||",PureAssertion(RelExpr(">=",ConstExpr(0),A1.delay_expr),sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2))
            #                   ,PureAssertion(RelExpr("<",ConstExpr(0),A1.delay_expr),G))
            F1 = RelExpr(">=",ConstExpr(0),A1.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A1.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                GG2p = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],A1.delay_expr),A2.delay(A1.delay_expr),LogicExpr("&&",cond,F2))
                if A2.ch_name in chset:
                    if GG2p == Fassn:
                        G2 = Fassn  
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                     ParamAssertion(A1.param_assn.bound_names,GG2p)))
                else:
                    Fc = LogicExpr("&&",RelExpr("<=",ConstExpr(0),VarExpr(A2.param_assn.bound_names[0])),RelExpr("<=",VarExpr(A2.param_assn.bound_names[0]),A1.delay_expr))
                    GG2c = sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn,LogicExpr("&&",cond,LogicExpr("&&",F2,Fc)))
                    if GG2p == Fassn and GG2c == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                                                 ParamAssertion(A1.param_assn.bound_names,GG2p),
                                                                 [(Ininf(A2.ch_name),ParamAssertion(A2.param_assn.bound_names,GG2c))]))
            return OpAssnOr(G1,G2)

        elif isinstance(A1,WaitInAssertion) and isinstance(A2,WaitAssertion):
            # if A1.ch_name in chset:
            #     G = WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
            #                          ParamAssertion(A2.param_assn.bound_names,sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn)))
            # else:
            #     G = InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
            #                               ParamAssertion(A2.param_assn.bound_names,sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn)),
            #                               [(Ininf(A1.ch_name),ParamAssertion(A1.param_assn.bound_names,sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])))))])
            # return OpAssn("||",PureAssertion(RelExpr(">=",ConstExpr(0),A2.delay_expr),sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0))))
            #                   ,PureAssertion(RelExpr("<",ConstExpr(0),A2.delay_expr),G))
            F1 = RelExpr(">=",ConstExpr(0),A2.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A2.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                GG2p = sync(chset,A1.delay(A2.delay_expr),A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],A2.delay_expr),LogicExpr("&&",cond,F2))
                if A1.ch_name in chset:
                    if GG2p == Fassn:
                        G2 = Fassn  
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                     ParamAssertion(A2.param_assn.bound_names,GG2p)))
                else:
                    Fc = LogicExpr("&&",RelExpr("<=",ConstExpr(0),VarExpr(A1.param_assn.bound_names[0])),RelExpr("<=",VarExpr(A1.param_assn.bound_names[0]),A2.delay_expr))
                    GG2c = sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",F2,Fc)))
                    if GG2p == Fassn and GG2c == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                                                 ParamAssertion(A2.param_assn.bound_names,GG2p),
                                                                 [(Ininf(A1.ch_name),ParamAssertion(A1.param_assn.bound_names,GG2c))]))
            return OpAssnOr(G1,G2)

        elif isinstance(A1,WaitAssertion) and isinstance(A2,WaitOutvAssertion):
            # if A2.ch_name in chset:
            #     G =  WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
            #                          ParamAssertion(A1.param_assn.bound_names,sync(chset,A1.param_assn.assn,
            #                                                                        A2.delay(VarExpr(A1.param_assn.bound_names[0])))))
            # else:
            #     G = InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
            #                               ParamAssertion(A1.param_assn.bound_names,sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])))),
            #                               [(Outinf(A2.ch_name,A2.expr),ParamAssertion(A2.param_assn.bound_names,sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn)))])
            # return OpAssn("||",PureAssertion(RelExpr(">=",ConstExpr(0),A1.delay_expr),sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2))
            #                   ,PureAssertion(RelExpr("<",ConstExpr(0),A1.delay_expr),G))
            F1 = RelExpr(">=",ConstExpr(0),A1.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A1.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                GG2p = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],A1.delay_expr),A2.delay(A1.delay_expr),LogicExpr("&&",cond,F2))
                if A2.ch_name in chset:
                    if GG2p == Fassn:
                        G2 = Fassn  
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                     ParamAssertion(A1.param_assn.bound_names,GG2p)))
                else:
                    Fc = LogicExpr("&&",RelExpr("<=",ConstExpr(0),VarExpr(A2.param_assn.bound_names[0])),RelExpr("<=",VarExpr(A2.param_assn.bound_names[0]),A1.delay_expr))
                    GG2c = sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn,LogicExpr("&&",cond,LogicExpr("&&",F2,Fc)))
                    if GG2p == Fassn and GG2c == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                                                 ParamAssertion(A1.param_assn.bound_names,GG2p),
                                                                 [(Outinf(A2.ch_name,A2.expr),ParamAssertion(A2.param_assn.bound_names,GG2c))]))
            return OpAssnOr(G1,G2)

        elif isinstance(A1,WaitOutvAssertion) and isinstance(A2,WaitAssertion):
            # if A1.ch_name in chset:
            #     G = WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
            #                          ParamAssertion(A2.param_assn.bound_names,sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn)))
            # else:
            #     G = InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
            #                               ParamAssertion(A2.param_assn.bound_names,sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn)),
            #                               [(Outinf(A1.ch_name,A1.expr),ParamAssertion(A1.param_assn.bound_names,sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])))))])
            # return OpAssn("||",PureAssertion(RelExpr(">=",ConstExpr(0),A2.delay_expr),sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0))))
            #                   ,PureAssertion(RelExpr("<",ConstExpr(0),A2.delay_expr),G))
            F1 = RelExpr(">=",ConstExpr(0),A2.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A2.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                GG2p = sync(chset,A1.delay(A2.delay_expr),A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],A2.delay_expr),LogicExpr("&&",cond,F2))
                if A1.ch_name in chset:
                    if GG2p == Fassn:
                        G2 = Fassn  
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                     ParamAssertion(A2.param_assn.bound_names,GG2p)))
                else:
                    Fc = LogicExpr("&&",RelExpr("<=",ConstExpr(0),VarExpr(A1.param_assn.bound_names[0])),RelExpr("<=",VarExpr(A1.param_assn.bound_names[0]),A2.delay_expr))
                    GG2c = sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",F2,Fc)))
                    if GG2p == Fassn and GG2c == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                                                 ParamAssertion(A2.param_assn.bound_names,GG2p),
                                                                 [(Outinf(A1.ch_name,A1.expr),ParamAssertion(A1.param_assn.bound_names,GG2c))]))
            return OpAssnOr(G1,G2)

        elif isinstance(A1,InterruptinfAssertion) and isinstance(A2,InterruptinfAssertion):
            if len(compat_rdy(A1.comm_specs,A2.comm_specs))==0:
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        G = sync(chset,i[1].assn,A2.delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0))))
                        if G != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        G = sync(chset,A1.delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0))))
                        if G != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                if len(comm) ==0:
                    return Fassn
                else:
                    return InterruptinfAssertion(PPathInvariant(A1.path_inv,A2.path_inv),comm)
            else:
                P = []
                for i,j in compat_rdy(A1.comm_specs,A2.comm_specs):
                    if isinstance(i[0],Ininf) and isinstance(j[0],Outinf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)).substVal(i[1].bound_names[1],j[0].expr.substVar(j[1].bound_names[0],ConstExpr(0)))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0))
                            P.append(sync(chset,l,r,cond))
                    elif isinstance(i[0],Outinf) and isinstance(j[0],Ininf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0)).substVal(j[1].bound_names[1],i[0].expr.substVar(i[1].bound_names[0],ConstExpr(0)))
                            P.append(sync(chset,l,r,cond))
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        G = sync(chset,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),A2,cond)
                        if G != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        G = sync(chset,A1,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),cond)
                        if G != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                if len(comm) ==0:
                    return OpAssnOr_mult(P)
                else:
                    dname = variant_name(bound_vars, "d")
                    return InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),ConstExpr(0),ParamAssertion([dname],OpAssnOr_mult("||",P)),comm)

        elif isinstance(A1,InterruptAssertion) and isinstance(A2,InterruptAssertion):
            if len(compat_rdy(A1.comm_specs,A2.comm_specs))==0:
                f1 = LogicExpr("&&",RelExpr("<",A1.delay_expr,A2.delay_expr),RelExpr("<",ConstExpr(0),A2.delay_expr))
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,f1))):
                    G1 = Fassn
                else:
                    fg1 = LogicExpr("||",LogicExpr("&&",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),ConstExpr(0)))
                                        ,LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),A1.delay_expr)))
                    GG1 = sync(chset,A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",f1,fg1)))
                    comm = []
                    for i in A1.comm_specs:
                        if i[0].ch_name not in chset:
                            fc1 = LogicExpr("&&",RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("||",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("<=",A2.delay_expr,ConstExpr(0))))
                            fc2 = LogicExpr("&&",LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))),LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr(">",A2.delay_expr,ConstExpr(0))))
                            fc = LogicExpr("||",fc1,fc2)
                            G = sync(chset,i[1].assn,A2.cond().delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",f1,fc)))
                            if G != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                    for i in A2.comm_specs:
                        if i[0].ch_name not in chset:
                            fc1 = LogicExpr("&&",RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("||",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("<=",A2.delay_expr,ConstExpr(0))))
                            fc2 = LogicExpr("&&",LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))),LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr(">",A2.delay_expr,ConstExpr(0))))
                            fc = LogicExpr("||",fc1,fc2)
                            G = sync(chset,A1.cond().delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,LogicExpr("&&",f1,fc)))
                            if G != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                    if len(comm)==0:
                        if GG1 == Fassn:
                            G1 = Fassn
                        else:
                            G1 = PureAssertion(f1,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,ParamAssertion(A1.param_assn.bound_names,GG1)))
                    else:
                        G1 = PureAssertion(f1,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,ParamAssertion(A1.param_assn.bound_names,GG1),comm))
                
                f2 = LogicExpr("&&",RelExpr(">",A1.delay_expr,A2.delay_expr),RelExpr("<",ConstExpr(0),A1.delay_expr))
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,f2))):
                    G2 = Fassn
                else:
                    fg2 = LogicExpr("||",LogicExpr("&&",RelExpr("<=",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),ConstExpr(0)))
                                        ,LogicExpr("&&",RelExpr(">",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),A2.delay_expr)))
                    GG2 = sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn,LogicExpr("&&",cond,LogicExpr("&&",f2,fg2)))
                    comm = []
                    for i in A1.comm_specs:
                        if i[0].ch_name not in chset:
                            fc1 = LogicExpr("&&",RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("||",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("<=",A2.delay_expr,ConstExpr(0))))
                            fc2 = LogicExpr("&&",LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))),LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr(">",A2.delay_expr,ConstExpr(0))))
                            fc = LogicExpr("||",fc1,fc2)
                            G = sync(chset,i[1].assn,A2.cond().delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",f2,fc)))
                            if G != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                    for i in A2.comm_specs:
                        if i[0].ch_name not in chset:
                            fc1 = LogicExpr("&&",RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("||",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("<=",A2.delay_expr,ConstExpr(0))))
                            fc2 = LogicExpr("&&",LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))),LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr(">",A2.delay_expr,ConstExpr(0))))
                            fc = LogicExpr("||",fc1,fc2)
                            G = sync(chset,A1.cond().delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,LogicExpr("&&",f2,fc)))
                            if G != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                    if len(comm)==0:
                        if GG2 == Fassn:
                            G2 = Fassn
                        else:
                            G2 = PureAssertion(f2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,ParamAssertion(A2.param_assn.bound_names,GG2)))
                    else:
                        G2 = PureAssertion(f2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,ParamAssertion(A2.param_assn.bound_names,GG2),comm))
                
                f3 = LogicExpr("||",RelExpr("==",A1.delay_expr,A2.delay_expr),LogicExpr("&&",RelExpr(">=",ConstExpr(0),A1.delay_expr),RelExpr(">=",ConstExpr(0),A2.delay_expr)))
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,f3))):
                    G3 = Fassn
                else:
                    dname = variant_name(bound_vars, "d")
                    fg3 = LogicExpr("||",LogicExpr("&&",RelExpr("<=",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),ConstExpr(0)))
                                        ,LogicExpr("&&",RelExpr(">",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),A2.delay_expr)))
                    GG3 = OpAssnOr(sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],VarExpr(dname)),A2.delay(VarExpr(dname)),LogicExpr("&&",cond,LogicExpr("&&",f3,fg3))),
                                   sync(chset,A1.delay(VarExpr(dname)),A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],VarExpr(dname)),LogicExpr("&&",cond,LogicExpr("&&",f3,fg3))))
                    comm = []
                    for i in A1.comm_specs:
                        if i[0].ch_name not in chset:
                            fc1 = LogicExpr("&&",RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("||",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("<=",A2.delay_expr,ConstExpr(0))))
                            fc2 = LogicExpr("&&",LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))),LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr(">",A2.delay_expr,ConstExpr(0))))
                            fc = LogicExpr("||",fc1,fc2)
                            G = sync(chset,i[1].assn,A2.cond().delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",f3,fc)))
                            if G != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                    for i in A2.comm_specs:
                        if i[0].ch_name not in chset:
                            fc1 = LogicExpr("&&",RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("||",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("<=",A2.delay_expr,ConstExpr(0))))
                            fc2 = LogicExpr("&&",LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))),LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr(">",A2.delay_expr,ConstExpr(0))))
                            fc = LogicExpr("||",fc1,fc2)
                            G = sync(chset,A1.cond().delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,LogicExpr("&&",f3,fc)))
                            if G != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,G)))
                    if len(comm)==0:
                        if GG3 == Fassn:
                            G3 = Fassn
                        else:
                            G3 = PureAssertion(f3,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,ParamAssertion([dname],GG3)))
                    else:
                        G3 = PureAssertion(f3,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,ParamAssertion([dname],GG3),comm))
                return OpAssnOr_mult([G1,G2,G3])

            else:
                P = []
                for i,j in compat_rdy(A1.comm_specs,A2.comm_specs):
                    if isinstance(i[0],Ininf) and isinstance(j[0],Outinf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)).substVal(i[1].bound_names[1],j[0].expr.substVar(j[1].bound_names[0],ConstExpr(0)))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0))
                            P.append(sync(chset,l,r,cond))
                    elif isinstance(i[0],Outinf) and isinstance(j[0],Ininf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0)).substVal(j[1].bound_names[1],i[0].expr.substVar(i[1].bound_names[0],ConstExpr(0)))
                            P.append(sync(chset,l,r,cond))
                G = OpAssnOr_mult(P)
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A2.delay_expr)))):
                    G1 = Fassn
                else:
                    GG1 = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A2.delay_expr)))
                    if GG1 == Fassn:
                        G1 = Fassn
                    else:
                        G1 = PureAssertion(RelExpr(">=",ConstExpr(0),A2.delay_expr),GG1)
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A1.delay_expr)))):
                    G2 = Fassn
                else:
                    GG2 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A1.delay_expr)))
                    if GG2 == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(RelExpr(">=",ConstExpr(0),A1.delay_expr),GG2)
                G = OpAssnOr_mult([G,G1,G2])
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        C = sync(chset,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),A2.cond(),cond)
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        C = sync(chset,A1.cond(),i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),cond)
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                if len(comm)>0:
                    dname = variant_name(bound_vars, "d")
                    return InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),ConstExpr(0),ParamAssertion([dname],G),comm)
                else:
                    return G
                
        elif isinstance(A1,InterruptAssertion) and isinstance(A2,InterruptinfAssertion):
            if len(compat_rdy(A1.comm_specs,A2.comm_specs))==0:
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        fc = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A1.delay_expr),RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)))
                                           ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A1.delay_expr),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)))))
                        C = sync(chset,i[1].assn,A2.delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,fc))
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        fc = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A1.delay_expr),RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)))
                                           ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A1.delay_expr),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)))))
                        C = sync(chset,A1.cond().delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,fc))
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                
                fg = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A1.delay_expr),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),ConstExpr(0)))
                                   ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A1.delay_expr),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),A1.delay_expr)))
                G = sync(chset,A1.param_assn.assn, A2.delay(VarExpr(A1.param_assn.bound_names[0])),LogicExpr("&&",cond,fg))
                if len(comm)>0:
                    return InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,ParamAssertion(A1.param_assn.bound_names,G),comm)
                else:
                    if G == Fassn:
                        return Fassn
                    else:
                        return WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,ParamAssertion(A1.param_assn.bound_names,G))
            else:
                P = []
                for i,j in compat_rdy(A1.comm_specs,A2.comm_specs):
                    if isinstance(i[0],Ininf) and isinstance(j[0],Outinf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)).substVal(i[1].bound_names[1],j[0].expr.substVar(j[1].bound_names[0],ConstExpr(0)))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0))
                            P.append(sync(chset,l,r,cond))
                    elif isinstance(i[0],Outinf) and isinstance(j[0],Ininf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0)).substVal(j[1].bound_names[1],i[0].expr.substVar(i[1].bound_names[0],ConstExpr(0)))
                            P.append(sync(chset,l,r,cond))
                G = OpAssnOr_mult(P)
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A1.delay_expr)))):
                    G2 = Fassn
                else:
                    GG2 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A1.delay_expr)))
                    if GG2 == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(RelExpr(">=",ConstExpr(0),A1.delay_expr),GG2)
                G = OpAssnOr_mult([G,G2])
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        C = sync(chset,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),A2,cond)
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        C = sync(chset,A1.cond(),i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),cond)
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                if len(comm)>0:
                    dname = variant_name(bound_vars, "d")
                    return InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),ConstExpr(0),ParamAssertion([dname],G),comm)
                else:
                    return G
                
        elif isinstance(A1,InterruptinfAssertion) and isinstance(A2,InterruptAssertion):
            if len(compat_rdy(A1.comm_specs,A2.comm_specs))==0:
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        fc = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)))
                                           ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A2.delay_expr),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A2.delay_expr),RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)))))
                        C = sync(chset,i[1].assn,A2.cond().delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,fc))
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        fc = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)))
                                           ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A2.delay_expr),LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A2.delay_expr),RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)))))
                        C = sync(chset,A1.delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,fc))
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))

                fg = LogicExpr("||",LogicExpr("&&",RelExpr(">=",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),ConstExpr(0)))
                                   ,LogicExpr("&&",RelExpr("<",ConstExpr(0),A2.delay_expr),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),A2.delay_expr)))
                G = sync(chset, A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn,LogicExpr("&&",cond,fg))        
                if len(comm)>0:
                    return InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,ParamAssertion(A2.param_assn.bound_names,G),comm)
                else:
                    if G == Fassn:
                        return Fassn
                    else:
                        return WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,ParamAssertion(A2.param_assn.bound_names,G))            
            
            else:
                P = []
                for i,j in compat_rdy(A1.comm_specs,A2.comm_specs):
                    if isinstance(i[0],Ininf) and isinstance(j[0],Outinf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)).substVal(i[1].bound_names[1],j[0].expr.substVar(j[1].bound_names[0],ConstExpr(0)))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0))
                            P.append(sync(chset,l,r,cond))
                    elif isinstance(i[0],Outinf) and isinstance(j[0],Ininf):
                        if i[0].ch_name not in chset:
                            raise NotImplementedError
                        else:
                            l = i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0))
                            r = j[1].assn.substVal(j[1].bound_names[0],ConstExpr(0)).substVal(j[1].bound_names[1],i[0].expr.substVar(i[1].bound_names[0],ConstExpr(0)))
                            P.append(sync(chset,l,r,cond))
                G = OpAssn_mult("||",P)
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A2.delay_expr)))):
                    G1 = Fassn
                else:
                    GG1 = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,RelExpr(">=",ConstExpr(0),A2.delay_expr)))
                    if GG1 == Fassn:
                        G1 = Fassn
                    else:
                        G1 = PureAssertion(RelExpr(">=",ConstExpr(0),A2.delay_expr),GG1)
                G = OpAssnOr_mult([G,G1])
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        C = sync(chset,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),A2.cond(),cond)
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        C = sync(chset,A1,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),cond)
                        if C != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
                if len(comm)>0:
                    dname = variant_name(bound_vars, "d")
                    return InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),ConstExpr(0),ParamAssertion([dname],G),comm)
                else:
                    return G
                
        elif isinstance(A1,InterruptinfAssertion) and isinstance(A2,InitAssertion):
            comm = []
            for i in A1.comm_specs:
                if i[0].ch_name not in chset:
                    C = sync(chset,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),A2,cond)
                    if C != Fassn:
                        comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
            dname = variant_name(bound_vars, "d")
            if len(comm)>0:
                return InterruptAssertion(PPathInvariant(A1.path_inv,id_inv),ConstExpr(0),ParamAssertion([dname],Fassn),comm)
            else:
                return Fassn
            
        elif isinstance(A1,InitAssertion) and isinstance(A2,InterruptinfAssertion):
            comm = []
            for i in A2.comm_specs:
                if i[0].ch_name not in chset:
                    C = sync(chset,A1,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),cond)
                    if C != Fassn:
                        comm.append((i[0],ParamAssertion(i[1].bound_names,C)))
            dname = variant_name(bound_vars, "d")
            if len(comm)>0:
                return InterruptAssertion(PPathInvariant(id_inv,A2.path_inv),ConstExpr(0),ParamAssertion([dname],Fassn),comm)
            else:
                return Fassn
        
        elif isinstance(A1,InterruptinfAssertion) and isinstance(A2,WaitAssertion):
            F1 = RelExpr(">=",ConstExpr(0),A2.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A2.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                comm = []
                for i in A1.comm_specs:
                    if i[0].ch_name not in chset:
                        Fc =LogicExpr("&&",F2,LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A2.delay_expr),RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0))))
                        GG2c = sync(chset,i[1].assn,A2.delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,Fc))
                        if GG2c != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,GG2c)))
                GG2p = sync(chset,A1.delay(A2.delay_expr),A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],A2.delay_expr),LogicExpr("&&",cond,F2))
                if len(comm)>0:
                    G2 = PureAssertion(F2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                        ParamAssertion(A2.param_assn.bound_names,GG2p),comm))
                else:
                    if GG2p == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                        ParamAssertion(A2.param_assn.bound_names,GG2p)))
            return OpAssnOr(G1,G2)
        
        elif isinstance(A1,WaitAssertion) and isinstance(A2,InterruptinfAssertion):
            F1 = RelExpr(">=",ConstExpr(0),A1.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A1.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                comm = []
                for i in A2.comm_specs:
                    if i[0].ch_name not in chset:
                        Fc =LogicExpr("&&",F2,LogicExpr("&&",RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr),RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0))))
                        GG2c = sync(chset,A1.delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,Fc))
                        if GG2c != Fassn:
                            comm.append((i[0],ParamAssertion(i[1].bound_names,GG2c)))
                GG2p = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],A1.delay_expr),A2.delay(A1.delay_expr),LogicExpr("&&",cond,F2))
                if len(comm)>0:
                    G2 = PureAssertion(F2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                        ParamAssertion(A1.param_assn.bound_names,GG2p),comm))
                else:
                    if GG2p == Fassn:
                        G2 = Fassn
                    else:
                        G2 = PureAssertion(F2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                        ParamAssertion(A1.param_assn.bound_names,GG2p)))
            return OpAssnOr(G1,G2)           

        elif isinstance(A1,InterruptAssertion) and isinstance(A2,InitAssertion):
            comm = []
            for i in A1.comm_specs:
                if i[0].ch_name not in chset:
                    Gc = sync(chset,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),A2,cond)
                    if Gc != Fassn:
                        comm.append((i[0],ParamAssertion(i[1].bound_names,Gc)))
            F = RelExpr(">=",ConstExpr(0),A1.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F))):
                G = Fassn
            else:
                GG = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,F))
                if GG == Fassn:
                    G = Fassn
                else:
                    G = PureAssertion(F,GG)
            if len(comm)>0:
                return InterruptAssertion(PPathInvariant(A1.path_inv,id_inv),ConstExpr(0),
                                          ParamAssertion(A1.param_assn.bound_names,G),comm)
            else:
                return G
        
        elif isinstance(A1,InitAssertion) and isinstance(A2,InterruptAssertion):
            comm = []
            for i in A2.comm_specs:
                if i[0].ch_name not in chset:
                    Gc = sync(chset,A1,i[1].assn.substVal(i[1].bound_names[0],ConstExpr(0)),cond)
                    if Gc != Fassn:
                        comm.append((i[0],ParamAssertion(i[1].bound_names,Gc)))
            F = RelExpr(">=",ConstExpr(0),A2.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F))):
                G = Fassn
            else:
                GG = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,F))
                if GG == Fassn:
                    G = Fassn
                else:
                    G = PureAssertion(F,GG)
            if len(comm)>0:
                return InterruptAssertion(PPathInvariant(id_inv,A2.path_inv),ConstExpr(0),
                                          ParamAssertion(A2.param_assn.bound_names,G),comm)
            else:
                return G

        elif isinstance(A1,InterruptAssertion) and isinstance(A2,WaitAssertion):
            F1 = RelExpr(">=",ConstExpr(0),A2.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A2.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                FF1 = RelExpr(">=",A1.delay_expr,A2.delay_expr)
                FF2 = RelExpr("<",A1.delay_expr,A2.delay_expr)
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,LogicExpr("&&",F2,FF1)))):
                    G21 = Fassn
                else:
                    comm = []
                    for i in A1.comm_specs:
                        if i[0].ch_name not in chset:
                            Fc = LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),RelExpr("<=",VarExpr(i[1].bound_names[0]),A2.delay_expr))
                            Gc = sync(chset,i[1].assn,A2.delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",F2,LogicExpr("&&",FF1,Fc))))
                            if Gc != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,Gc)))
                    G21p = sync(chset,A1.delay(A2.delay_expr),A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],A2.delay_expr),LogicExpr("&&",cond,LogicExpr("&&",F2,FF1)))
                    if len(comm)>0:
                        G21 = PureAssertion(FF1,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                       ParamAssertion(A2.param_assn.bound_names,G21p),comm))
                    else:
                        if G21p == Fassn:
                            G21 = Fassn
                        else:
                            G21 = PureAssertion(FF1,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                       ParamAssertion(A2.param_assn.bound_names,G21p)))
                
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,LogicExpr("&&",F2,FF2)))):
                    G22 = Fassn
                else:
                    comm = []
                    for i in A1.comm_specs:
                        if i[0].ch_name not in chset:
                            Fc1 = LogicExpr("&&",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)))
                            Fc2 = LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr)))
                            Fc = LogicExpr("||",Fc1,Fc2)
                            Gc = sync(chset,i[1].assn,A2.delay(VarExpr(i[1].bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",F2,LogicExpr("&&",FF2,Fc))))
                            if Gc != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,Gc)))
                    Fp1 = LogicExpr("&&",RelExpr("<=",A1.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),ConstExpr(0)))
                    Fp2 = LogicExpr("&&",RelExpr(">",A1.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A1.param_assn.bound_names[0]),A1.delay_expr))
                    Fp = LogicExpr("||",Fp1,Fp2)
                    G22p = sync(chset,A1.param_assn.assn,A2.delay(VarExpr(A1.param_assn.bound_names[0])),LogicExpr("&&",cond,LogicExpr("&&",F2,LogicExpr("&&",FF2,Fp))))
                    if len(comm)>0:
                        G22 = PureAssertion(FF2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                       ParamAssertion(A1.param_assn.bound_names,G22p),comm))
                    else:
                        if G22p == Fassn:
                            G22 = Fassn
                        else:
                            G22 = PureAssertion(FF2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                       ParamAssertion(A1.param_assn.bound_names,G22p)))
                G2 = OpAssnOr(G21,G22)  
                if G2 != Fassn:
                    G2 = PureAssertion(F2,G2)          
            return OpAssnOr(G1,G2) 
        
        elif isinstance(A1,WaitAssertion) and isinstance(A2,InterruptAssertion):
            F1 = RelExpr(">=",ConstExpr(0),A1.delay_expr)
            F2 = RelExpr("<",ConstExpr(0),A1.delay_expr)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F1))):
                G1 = Fassn
            else:
                GG1 = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,F1))
                if GG1 == Fassn:
                    G1 = Fassn
                else:
                    G1 = PureAssertion(F1,GG1)
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F2))):
                G2 = Fassn
            else:
                FF1 = RelExpr(">=",A2.delay_expr,A1.delay_expr)
                FF2 = RelExpr("<",A2.delay_expr,A1.delay_expr)
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,LogicExpr("&&",F2,FF1)))):
                    G21 = Fassn
                else:
                    comm = []
                    for i in A2.comm_specs:
                        if i[0].ch_name not in chset:
                            Fc = LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),RelExpr("<=",VarExpr(i[1].bound_names[0]),A1.delay_expr))
                            Gc = sync(chset,A1.delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,LogicExpr("&&",F2,LogicExpr("&&",FF1,Fc))))
                            if Gc != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,Gc)))
                    G21p = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],A1.delay_expr),A2.delay(A1.delay_expr),LogicExpr("&&",cond,LogicExpr("&&",F2,FF1)))
                    if len(comm)>0:
                        G21 = PureAssertion(FF1,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                       ParamAssertion(A1.param_assn.bound_names,G21p),comm))
                    else:
                        if G21p == Fassn:
                            G21 = Fassn
                        else:
                            G21 = PureAssertion(FF1,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A1.delay_expr,
                                       ParamAssertion(A1.param_assn.bound_names,G21p)))
                
                if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,LogicExpr("&&",F2,FF2)))):
                    G22 = Fassn
                else:
                    comm = []
                    for i in A2.comm_specs:
                        if i[0].ch_name not in chset:
                            Fc1 = LogicExpr("&&",RelExpr("<=",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(i[1].bound_names[0]),ConstExpr(0)))
                            Fc2 = LogicExpr("&&",RelExpr(">",A2.delay_expr,ConstExpr(0)),LogicExpr("&&",RelExpr(">=",VarExpr(i[1].bound_names[0]),ConstExpr(0)),RelExpr("<=",VarExpr(i[1].bound_names[0]),A2.delay_expr)))
                            Fc = LogicExpr("||",Fc1,Fc2)
                            Gc = sync(chset,A1.delay(VarExpr(i[1].bound_names[0])),i[1].assn,LogicExpr("&&",cond,LogicExpr("&&",F2,LogicExpr("&&",FF2,Fc))))
                            if Gc != Fassn:
                                comm.append((i[0],ParamAssertion(i[1].bound_names,Gc)))
                    Fp1 = LogicExpr("&&",RelExpr("<=",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),ConstExpr(0)))
                    Fp2 = LogicExpr("&&",RelExpr(">",A2.delay_expr,ConstExpr(0)),RelExpr("==",VarExpr(A2.param_assn.bound_names[0]),A2.delay_expr))
                    Fp = LogicExpr("||",Fp1,Fp2)
                    G22p = sync(chset,A1.delay(VarExpr(A2.param_assn.bound_names[0])),A2.param_assn.assn,LogicExpr("&&",cond,LogicExpr("&&",F2,LogicExpr("&&",FF2,Fp))))
                    if len(comm)>0:
                        G22 = PureAssertion(FF2,InterruptAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                       ParamAssertion(A2.param_assn.bound_names,G22p),comm))
                    else:
                        if G22p == Fassn:
                            G22 = Fassn
                        else:
                            G22 = PureAssertion(FF2,WaitAssertion(PPathInvariant(A1.path_inv,A2.path_inv),A2.delay_expr,
                                       ParamAssertion(A2.param_assn.bound_names,G22p)))
                G2 = OpAssnOr(G21,G22)  
                if G2 != Fassn:
                    G2 = PureAssertion(F2,G2)          
            return OpAssnOr(G1,G2) 
        
        elif isinstance(A1,WaitAssertion) and isinstance(A2,InitAssertion):
            F = RelExpr("<=",A1.delay_expr,ConstExpr(0))
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F))):
                return Fassn
            else:
                G = sync(chset,A1.param_assn.assn.substVal(A1.param_assn.bound_names[0],ConstExpr(0)),A2,LogicExpr("&&",cond,F))
                if G == Fassn:
                    return Fassn
                else:
                    return PureAssertion(F,G)
        
        elif isinstance(A1,InitAssertion) and isinstance(A2,WaitAssertion):
            F = RelExpr("<=",A2.delay_expr,ConstExpr(0))
            if wl_proven(eexpr_to_expr(LogicExpr("&&",cond,F))):
                return Fassn
            else:
                G = sync(chset,A1,A2.param_assn.assn.substVal(A2.param_assn.bound_names[0],ConstExpr(0)),LogicExpr("&&",cond,F))
                if G == Fassn:
                    return Fassn
                else:
                    return PureAssertion(F,G)
            
        elif isinstance(A1,InterruptinfAssertion) and isinstance(A2,WaitInAssertion):
            return sync(chset,A1,InterruptinfAssertion(A2.path_inv,[(Ininf(A2.ch_name),A2.param_assn)]),cond)
        
        elif isinstance(A1,WaitInAssertion) and isinstance(A2,InterruptinfAssertion):
            return sync(chset,InterruptinfAssertion(A1.path_inv,[(Ininf(A1.ch_name),A1.param_assn)]),A2,cond)
        
        elif isinstance(A1,InterruptinfAssertion) and isinstance(A2,WaitOutvAssertion):
            return sync(chset,A1,InterruptinfAssertion(A2.path_inv,[(Outinf(A2.ch_name,A2.expr),A2.param_assn)]),cond)
        
        elif isinstance(A1,WaitOutvAssertion) and isinstance(A2,InterruptinfAssertion):
            return sync(chset,InterruptinfAssertion(A1.path_inv,[(Outinf(A1.ch_name,A1.expr),A1.param_assn)]),A2,cond)
        
        elif isinstance(A1,InterruptAssertion) and isinstance(A2,WaitInAssertion):
            return sync(chset,A1,InterruptinfAssertion(A2.path_inv,[(Ininf(A2.ch_name),A2.param_assn)]),cond)
        
        elif isinstance(A1,WaitInAssertion) and isinstance(A2,InterruptAssertion):
            return sync(chset,InterruptinfAssertion(A1.path_inv,[(Ininf(A1.ch_name),A1.param_assn)]),A2,cond)
        
        elif isinstance(A1,InterruptAssertion) and isinstance(A2,WaitOutvAssertion):
            return sync(chset,A1,InterruptinfAssertion(A2.path_inv,[(Outinf(A2.ch_name,A2.expr),A2.param_assn)]),cond)
        
        elif isinstance(A1,WaitOutvAssertion) and isinstance(A2,InterruptAssertion):
            return sync(chset,InterruptinfAssertion(A1.path_inv,[(Outinf(A1.ch_name,A1.expr),A1.param_assn)]),A2,cond)

        elif isinstance(A1,RecursionVar) and not isinstance(A2,RecursionVar):
            sucess = 0
            for s in rec_tup:
                # rec_tup.append((A1,A2,Rname,inv))
                assert isinstance(s[0], RecAssertion) and isinstance(s[1], RecAssertion)
                if s[0].rec_var == A1.name:
                    g = s[1].assn


        else:
            print(A1)
            print(A2)
            raise NotImplementedError

        

    def sync_tuple(T: tuple) -> Assertion:
        assert isinstance(T,tuple) and len(T)==3
        init_txt = T[1].get("init","true")
        init = expr_to_eexpr(parse_expr_with_meta(init_txt))
        if isinstance(T[0],tuple):
            init_txt1 = T[0][1].get("init","true")
            init1 = expr_to_eexpr(parse_expr_with_meta(init_txt1))
            if wl_prove(eexpr_to_expr(LogicExpr("->",init,init1))):
                left = sync_tuple(T[0])
            else:
                print("wrong init")
                raise NotImplementedError
        elif isinstance(T[0],dict):
            hp = parse_hp_with_meta(T[0]["P"])
            hpa = seq_hcsp_to_assn(hp)
            left = add_pn_assn(T[0]["pn"],hpa)
            # print(left)
        else:
            raise NotImplementedError

        if isinstance(T[2],tuple):
            init_txt2 = T[2][1].get("init","true")
            init2 = expr_to_eexpr(parse_expr_with_meta(init_txt2))
            if wl_prove(eexpr_to_expr(LogicExpr("->",init,init2))):
                right = sync_tuple(T[2])
            else:
                raise NotImplementedError
        elif isinstance(T[2],dict):
            hp = parse_hp_with_meta(T[2]["P"])
            hpa = seq_hcsp_to_assn(hp)
            right = add_pn_assn(T[2]["pn"],hpa)
            # print(right)
        else:
            print("wrong process")
            raise NotImplementedError
        # print(left)
        # print(right)
        # init_txt = input("Enter an init: ")
        chset = T[1]["chset"]
        if "recinv" in T[1]:
            rec_tup_inv.append(T[1]["recinv"])
        return sync(chset,left,right,init)
    

    def sync_hcsp(T: hcsp.PParallel) -> Assertion:
        assert isinstance(T, hcsp.PParallel)
        if isinstance(T.hp1, hcsp.PParallel):
            left = sync_hcsp(T.hp1)
        elif isinstance(T.hp1, hcsp.Pnseqhp):
            shp = T.hp1.hp
            hpa = seq_hcsp_to_assn(shp)
            left = add_pn_assn(T.hp1.pn,hpa)
            # print(left)
        else:
            raise NotImplementedError

        if isinstance(T.hp2, hcsp.PParallel):
            right = sync_hcsp(T.hp2)
        elif isinstance(T.hp2, hcsp.Pnseqhp):
            shp = T.hp2.hp
            hpa = seq_hcsp_to_assn(shp)
            right = add_pn_assn(T.hp2.pn,hpa)
            # print(left)
        else:
            raise NotImplementedError
        # print(left)
        # print(right)
        # init_txt = input("Enter an init: ")
        chset = set(T.chs)
        return sync(chset,left,right)
    
    if isinstance(T,tuple):
        return sync_tuple(T)
    elif isinstance(T, hcsp.PParallel):
        return sync_hcsp(T)
    elif isinstance(T,hcsp.HCSP):
        return seq_hcsp_to_assn(T)
    else:
        hp = parse_hp_with_meta(T)
        hpa = seq_hcsp_to_assn(hp)
        return hpa
    

def change(form: expr.Expr):
    V = form.get_vars()
    fform = expr_to_eexpr(form)
    fform = add_0_eexpr(fform)
    for v in V:
        fform = LogicExpr("&&", fform, RelExpr("==",VarExpr(v), VarExpr(v+"00")))
    return fform

def sync_post(pret, assn: Assertion, postt, rec_tup_list):
    rec_tup_inv = {}
    bound_vars = []

    def prop(pre: EExpr, assn: Assertion, post: EExpr):
        nonlocal rec_tup_inv
        nonlocal bound_vars

        if isinstance(assn, InitAssertion):
            if wl_prove(eexpr_to_expr(LogicExpr("->", pre, post))):
                return True
            else:
                print("false") 
                print(pre)
                print(post)
                return False
    
        elif isinstance(assn, OpAssn):
            if assn.op == "||":
                return prop(pre, assn.assns[0], post) and prop(pre, assn.assns[1], post)
            else:
                raise NotImplementedError
    
        elif isinstance(assn, WaitAssertion):
            g1 = prop(LogicExpr("&&",pre, RelExpr(">",assn.delay_expr,ConstExpr(0))), assn.param_assn.assn.substVal(assn.param_assn.bound_names[0], assn.delay_expr), post)
            g2 = prop(LogicExpr("&&",pre, RelExpr("<=",assn.delay_expr,ConstExpr(0))), assn.param_assn.assn.substVal(assn.param_assn.bound_names[0], ConstExpr(0)), post)
            return  g1 and g2
        
        elif isinstance(assn, PureAssertion):
            return prop(LogicExpr("&&",pre, assn.expr), assn.assn, post)
        
        elif isinstance(assn, VarSubstAssertion):
            varname = variant_name(bound_vars, assn.var)
            pree = ExistsExpr([varname],LogicExpr("&&",pre.substVar(assn.var,VarExpr(varname)),RelExpr("==",VarExpr(assn.var),assn.expr.substVar(assn.var,VarExpr(varname)))))
            return prop(pree, assn.start_assn, post)
    
        elif isinstance(assn,VarsSubstAssertion):
            varnames = []
            varexprs = []
            for var in assn.vars:
                varname = variant_name(bound_vars, var)
                varnames.append(varname)
                varexprs.append(VarExpr(varname))
            pree = pre.substVars(assn.vars,varexprs)
            for i in range(0,len(assn.vars)):
                pree = LogicExpr("&&",pree,RelExpr("==",VarExpr(assn.vars[i]),assn.exprs[i].substVars(assn.vars,varexprs)))
            pree = ExistsExpr(varnames,pree)
            return prop(pree, assn.start_assn, post)
        
        elif isinstance(assn, RecAssertion):
            for s in rec_tup_list:
                if s[0] == assn.rec_var:
                    t = parse_expr_with_meta(s[1])
                    if wl_prove(eexpr_to_expr(LogicExpr("->", pre, expr_to_eexpr(t)))):
                        rec_tup_inv[assn.rec_var]=expr_to_eexpr(t)
                        return prop(change(t), assn.assn, post)
                    else:
                        print("wrong inv")
                        raise NotImplementedError

        elif isinstance(assn, RecursionVar):
            if assn.name in rec_tup_inv:
                if wl_prove(eexpr_to_expr(LogicExpr("->", pre, rec_tup_inv[assn.name]))):
                    # print("true inv")
                    return True
                else:
                    print("false inv")
                    print(pre)
                    print(post)
                    raise NotImplementedError
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    
    pre = change(parse_expr_with_meta(pret))
    post = expr_to_eexpr(parse_expr_with_meta(postt))
    return prop(pre, assn, post)



def sync_post_tr(pret, assn: Assertion, postt, rec_tup_list):
    rec_tup_inv = {}
    bound_vars = []

    def pathInvcond(pInv: PathInvariant, subd: dict):
        # print(subd)
        # print(pInv)
        # nonlocal ODEINV
            
        if isinstance(pInv, IdPathInvariant):
            # print("end")
            return BConstExpr(True),subd
        
        elif isinstance(pInv,ExprPathInvariant):
            # print("end")
            return BConstExpr(True),subd
        
        elif isinstance(pInv, SubstVarPathInvariant):
            subexpr = pInv.expr
            for vard in subd:
                subexpr = subexpr.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))
            if pInv.var in subd:
                subd[pInv.var] = subd[pInv.var]+1
            else:
                subd[pInv.var] = 1
            subeq = RelExpr("==", VarExpr(pInv.var+str(subd[pInv.var])+"I"), subexpr)
            e,d=pathInvcond(pInv.start_path_inv, subd)
            return LogicExpr("&&", subeq, e),d
        
        elif isinstance(pInv, SubstVarsPathInvariant):
            subexprs = []
            for subexpr in pInv.exprs:
                for vard in subd:
                    subexpr = subexpr.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))
                subexprs.append(subexpr)
            for var in pInv.vars:    
                if var in subd:
                    subd[var] = subd[var]+1
                else:
                    subd[var] = 1
            subeqs = []
            for i in range(0,len(pInv.vars)):
                subeq = RelExpr("==", VarExpr(pInv.vars[i]+str(subd[pInv.vars[i]])+"I"), subexprs[i])
                subeqs.append(subeq)
            subeqss = LogicExpr_mult("&&",subeqs)
            e,d=pathInvcond(pInv.start_path_inv, subd)
            # print(pathInvcond(pInv.start_path_inv, subd)[1])
            return LogicExpr("&&", subeqss, e),d
        
        elif isinstance(pInv, PPathInvariant):
            if subd != {}:
                raise NotImplementedError
            e1,d1 = pathInvcond(pInv.path_inv1, subd)
            e2,d2 = pathInvcond(pInv.path_inv2, subd)
            d={}
            d.update(d1)
            d.update(d2)
            return LogicExpr("&&",e1,e2),d

    def prop(pre: EExpr, assn: Assertion, post: EExpr):
        nonlocal rec_tup_inv
        nonlocal bound_vars

        if isinstance(assn, InitAssertion):
            return True
    
        elif isinstance(assn, OpAssn):
            if assn.op == "||":
                return prop(pre, assn.assns[0], post) and prop(pre, assn.assns[1], post)
            else:
                raise NotImplementedError
    
        elif isinstance(assn, WaitAssertion):
            g1 = prop(LogicExpr("&&",pre, RelExpr(">",assn.delay_expr,ConstExpr(0))), assn.param_assn.assn.substVal(assn.param_assn.bound_names[0], assn.delay_expr), post)
            g2 = prop(LogicExpr("&&",pre, RelExpr("<=",assn.delay_expr,ConstExpr(0))), assn.param_assn.assn.substVal(assn.param_assn.bound_names[0], ConstExpr(0)), post)
            subexpr,d = pathInvcond(assn.path_inv,{})
            subpost = post
            for vard in d:
                subpost = subpost.substVar(vard, VarExpr(vard+str(d[vard])+"I"))
            pree = LogicExpr("&&",pre, RelExpr(">",assn.delay_expr,ConstExpr(0)))
            pree = LogicExpr("&&",pree, subexpr)
            pree = LogicExpr("&&",pree, RelExpr(">=",VarExpr("t"),ConstExpr(0)))
            pree = LogicExpr("&&",pree, RelExpr("<=",VarExpr("t"),assn.delay_expr))
            if wl_prove(eexpr_to_expr(LogicExpr("->",pree,subpost))):
                # print("subgoal")
                return  g1 and g2
            else:
                print("wrong pathinv")
                print(assn.path_inv)
                print(pree)
                print(subpost)
                raise NotImplementedError
        
        elif isinstance(assn, PureAssertion):
            return prop(LogicExpr("&&",pre, assn.expr), assn.assn, post)
        
        elif isinstance(assn, VarSubstAssertion):
            varname = variant_name(bound_vars, assn.var)
            pree = ExistsExpr([varname],LogicExpr("&&",pre.substVar(assn.var,VarExpr(varname)),RelExpr("==",VarExpr(assn.var),assn.expr.substVar(assn.var,VarExpr(varname)))))
            return prop(pree, assn.start_assn, post)
    
        elif isinstance(assn,VarsSubstAssertion):
            varnames = []
            varexprs = []
            for var in assn.vars:
                varname = variant_name(bound_vars, var)
                varnames.append(varname)
                varexprs.append(VarExpr(varname))
            pree = pre.substVars(assn.vars,varexprs)
            for i in range(0,len(assn.vars)):
                pree = LogicExpr("&&",pree,RelExpr("==",VarExpr(assn.vars[i]),assn.exprs[i].substVars(assn.vars,varexprs)))
            pree = ExistsExpr(varnames,pree)
            return prop(pree, assn.start_assn, post)
        
        elif isinstance(assn, RecAssertion):
            for s in rec_tup_list:
                if s[0] == assn.rec_var:
                    t = parse_expr_with_meta(s[1])
                    if wl_prove(eexpr_to_expr(LogicExpr("->", pre, expr_to_eexpr(t)))):
                        rec_tup_inv[assn.rec_var]=expr_to_eexpr(t)
                        return prop(change(t), assn.assn, post)
                    else:
                        print("wrong inv")
                        raise NotImplementedError

        elif isinstance(assn, RecursionVar):
            if assn.name in rec_tup_inv:
                if wl_prove(eexpr_to_expr(LogicExpr("->", pre, rec_tup_inv[assn.name]))):
                    # print("true inv")
                    return True
                else:
                    print("false inv")
                    print(pre)
                    print(post)
                    raise NotImplementedError
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    
    pre = change(parse_expr_with_meta(pret))
    post = expr_to_eexpr(parse_expr_with_meta(postt))
    return prop(pre, assn, post)



def sync_post_both(pre, assn: Assertion, posts, postt, rec_tup_list, odehps):
    rec_tup_inv = {}
    bound_vars = []
    ODEINV = []

        
    def ppathInvcond(pInv: PathInvariant, subd: dict, pre:EExpr, delay: EExpr):
        nonlocal ODEINV

        if isinstance(pInv, PPathInvariant):
            if subd != {}:
                raise NotImplementedError
            e1,d1 = ppathInvcond(pInv.path_inv1, subd, pre, delay)
            e2,d2 = ppathInvcond(pInv.path_inv2, subd, pre, delay)
            d={}
            d.update(d1)
            d.update(d2)
            return LogicExpr("&&",e1,e2),d
        else:
            exprL = []
            while isinstance(pInv, SubstVarPathInvariant) or isinstance(pInv, SubstVarsPathInvariant): 
                if isinstance(pInv, SubstVarPathInvariant):
                    subexpr = pInv.expr
                    for vard in subd:
                        subexpr = subexpr.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))
                    if pInv.var in subd:
                        subd[pInv.var] = subd[pInv.var]+1
                    else:
                        subd[pInv.var] = 1
                    subeq = RelExpr("==", VarExpr(pInv.var+str(subd[pInv.var])+"I"), subexpr)
                    exprL.append(subeq)
                    
                if isinstance(pInv, SubstVarsPathInvariant):
                    subexprs = []
                    for subexpr in pInv.exprs:
                        for vard in subd:
                            subexpr = subexpr.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))
                        subexprs.append(subexpr)
                    for var in pInv.vars:    
                        if var in subd:
                            subd[var] = subd[var]+1
                        else:
                            subd[var] = 1
                    for i in range(0,len(pInv.vars)):
                        subeq = RelExpr("==", VarExpr(pInv.vars[i]+str(subd[pInv.vars[i]])+"I"), subexprs[i])
                        exprL.append(subeq)

                pInv = pInv.start_path_inv
            
            if isinstance(pInv, IdPathInvariant) or isinstance(pInv, ExprPathInvariant):
                return LogicExpr_mult("&&",exprL),subd
            
            elif isinstance(pInv, ODEPathInvariant):
                subpd = subd.copy()
                if pInv.pn is not None:
                    cons = add_pn_eexpr(pInv.pn, pInv.cons)
                    for var,_ in pInv.eqs:    
                        if pInv.pn+var in subd:
                            subd[pInv.pn+var] = subd[pInv.pn+var]+1
                        else:
                            subd[pInv.pn+var] = 1
                else:
                    cons = pInv.cons
                    for var,_ in pInv.eqs:    
                        if var in subd:
                            subd[var] = subd[var]+1
                        else:
                            subd[var] = 1

                if pInv.sols is not None:
                    # print(pInv.sols)
                    # print(len(pInv.sols[1])) 
                    subexprs = []
                    solcons = []
                    for subexpr in pInv.sols[1]:
                        for vard in subd:
                            subexpr = subexpr.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))
                        subexprs.append(subexpr)
                    for i in range(0,len(pInv.sols[0])):
                        subeq = RelExpr("==", VarExpr(pInv.sols[0][i]+str(subd[pInv.sols[0][i]])+"I"), subexprs[i])
                        solcons.append(subeq)
                
                inv = pInv.expr
                for vard in subd:
                    cons = cons.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))
                    inv = inv.substVar(vard, VarExpr(vard+str(subd[vard])+"I"))

                ex = 0
                for INV in ODEINV:
                    if wl_prove(eexpr_to_expr(LogicExpr('<->', INV['init'], LogicExpr_mult("&&",exprL)))) and \
                        INV['subpd'] == subpd and INV['subd'] == subd and INV['eqs'] == pInv.eqs and \
                        INV['unsol'] == pInv.unsol and INV['pn'] == pInv.pn and INV['inv'] == pInv.expr:
                        ex = 1
                        INV['pre'].append(LogicExpr("&&", pre, RelExpr(">",delay,ConstExpr(0))))
                        if pInv.sols is not None:
                            g = []
                            g.append(pre)
                            g.append(cons)
                            g.append(RelExpr(">",delay,ConstExpr(0)))
                            g.append(RelExpr(">=",VarExpr("t"),ConstExpr(0)))
                            g.append(RelExpr("<",VarExpr("t"),delay))
                            INV['cons'].append(LogicExpr_mult("&&",exprL+g+solcons))
                        else:
                            g = []
                            g.append(pre)
                            g.append(cons)
                            g.append(RelExpr(">",delay,ConstExpr(0)))
                            INV['cons'].append(LogicExpr_mult("&&",exprL+g))
                if ex == 0 :
                    INV = {}
                    INV['init'] = LogicExpr_mult("&&",exprL)
                    INV['subpd'] = subpd
                    INV['subd'] = subd
                    INV['eqs'] = pInv.eqs
                    INV['unsol'] = pInv.unsol
                    INV['pn'] = pInv.pn
                    INV['inv'] = pInv.expr
                    INV['pre']=[LogicExpr("&&", pre, RelExpr(">",delay,ConstExpr(0)))]
                    if pInv.sols is not None:
                        g = []
                        g.append(pre)
                        g.append(cons)
                        g.append(RelExpr(">",delay,ConstExpr(0)))
                        g.append(RelExpr(">=",VarExpr("t"),ConstExpr(0)))
                        g.append(RelExpr("<",VarExpr("t"),delay))
                        INV['cons']=[LogicExpr_mult("&&",exprL+g+solcons)]
                    else:
                        g = []
                        g.append(pre)
                        g.append(cons)
                        g.append(RelExpr(">",delay,ConstExpr(0)))
                        INV['cons']=[LogicExpr_mult("&&",exprL+g)]
                    ODEINV.append(INV)
                
                exprL.append(inv)
                return LogicExpr_mult("&&",exprL),subd

                        
    def prop(pre: EExpr, assn: Assertion, post: EExpr, postt: EExpr):
        nonlocal rec_tup_inv
        nonlocal bound_vars

        if isinstance(assn, InitAssertion):
            if wl_prove(eexpr_to_expr(LogicExpr("->", pre, post))):
                return True
            else:
                print("false") 
                print(pre)
                print(post)
                return False
    
        elif isinstance(assn, OpAssn):
            if assn.op == "||":
                return prop(pre, assn.assns[0], post, postt) and prop(pre, assn.assns[1], post, postt)
            else:
                raise NotImplementedError
    
        elif isinstance(assn, WaitAssertion):
            g1 = prop(LogicExpr("&&",pre, RelExpr(">",assn.delay_expr,ConstExpr(0))), assn.param_assn.assn.substVal(assn.param_assn.bound_names[0], assn.delay_expr), post, postt)
            g2 = prop(LogicExpr("&&",pre, RelExpr("<=",assn.delay_expr,ConstExpr(0))), assn.param_assn.assn.substVal(assn.param_assn.bound_names[0], ConstExpr(0)), post, postt)
            subexpr,d = ppathInvcond(assn.path_inv,{},pre, assn.delay_expr)
            subpost = postt
            for vard in d:
                subpost = subpost.substVar(vard, VarExpr(vard+str(d[vard])+"I"))
            pree = LogicExpr("&&",pre, RelExpr(">",assn.delay_expr,ConstExpr(0)))
            pree = LogicExpr("&&",pree, subexpr)
            pree = LogicExpr("&&",pree, RelExpr(">=",VarExpr("t"),ConstExpr(0)))
            pree = LogicExpr("&&",pree, RelExpr("<=",VarExpr("t"),assn.delay_expr))
            if wl_prove(eexpr_to_expr(LogicExpr("->",pree,subpost))):
                # print("subgoal")
                return  g1 and g2
            else:
                print("wrong pathinv")
                print(assn.path_inv)
                print(pree)
                print(subpost)
                raise NotImplementedError
        
        elif isinstance(assn, PureAssertion):
            return prop(LogicExpr("&&",pre, assn.expr), assn.assn, post, postt)
        
        elif isinstance(assn, VarSubstAssertion):
            varname = variant_name(bound_vars, assn.var)
            pree = ExistsExpr([varname],LogicExpr("&&",pre.substVar(assn.var,VarExpr(varname)),RelExpr("==",VarExpr(assn.var),assn.expr.substVar(assn.var,VarExpr(varname)))))
            return prop(pree, assn.start_assn, post, postt)
    
        elif isinstance(assn,VarsSubstAssertion):
            varnames = []
            varexprs = []
            for var in assn.vars:
                varname = variant_name(bound_vars, var)
                varnames.append(varname)
                varexprs.append(VarExpr(varname))
            pree = pre.substVars(assn.vars,varexprs)
            for i in range(0,len(assn.vars)):
                pree = LogicExpr("&&",pree,RelExpr("==",VarExpr(assn.vars[i]),assn.exprs[i].substVars(assn.vars,varexprs)))
            pree = ExistsExpr(varnames,pree)
            return prop(pree, assn.start_assn, post, postt)
        
        elif isinstance(assn, RecAssertion):
            for s in rec_tup_list:
                if s[0] == assn.rec_var:
                    t = parse_expr_with_meta(s[1])
                    if wl_prove(eexpr_to_expr(LogicExpr("->", pre, expr_to_eexpr(t)))):
                        rec_tup_inv[assn.rec_var]=expr_to_eexpr(t)
                        return prop(change(t), assn.assn, post, postt)
                    else:
                        print("wrong inv")
                        raise NotImplementedError

        elif isinstance(assn, RecursionVar):
            if assn.name in rec_tup_inv:
                if wl_prove(eexpr_to_expr(LogicExpr("->", pre, rec_tup_inv[assn.name]))):
                    # print("true inv")
                    return True
                else:
                    print("false inv")
                    print(pre)
                    raise NotImplementedError
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
        
    def test(INVL,ODEL):
        cond = []
        inv = []
        for ODE in ODEL:
            cc, ii = verify_ode(ODE)
            cond.append(cc)
            inv.append(ii)
        exx = True
        for INV in INVL:
            # print(INV)
            pINV = []
            for i in range(0,len(ODEL)):
                if INV['eqs'] == ODEL[i].eqs:
                    d = INV['subd']
                    pd = INV['subpd']
                    io = INV['inv']
                    cc = cond[i]
                    ii = inv[i]
                    cons = expr_to_eexpr(ODEL[i].constraint)
                    if INV['pn'] is not None:
                        cc = add_pn_eexpr(INV['pn'], cc)
                        ii = add_pn_eexpr(INV['pn'], ii)
                        cons = add_pn_eexpr(INV['pn'], cons)
                    for vard in d:
                        ii = ii.substVar(vard, VarExpr(vard+str(d[vard])+"I"))
                        cons = cons.substVar(vard, VarExpr(vard+str(d[vard])+"I"))
                        io = io.substVar(vard, VarExpr(vard+str(d[vard])+"I"))
                    for vard in pd:
                        cc = cc.substVar(vard, VarExpr(vard+str(pd[vard])+"I"))
                    ex = 0
                    for j in range(0,len(INV['pre'])):
                        if wl_prove(eexpr_to_expr(LogicExpr("->", LogicExpr("&&", LogicExpr("&&", INV['pre'][j], INV['init']), ii), io))) and\
                           wl_prove(eexpr_to_expr(LogicExpr("->", INV['cons'][j], cons))):
                            continue
                        else:
                            ex = 1
                            break
                    if ex == 0:
                        pINV.append(cc)
            if wl_prove(eexpr_to_expr(LogicExpr("->", LogicExpr("&&", LogicExpr_mult("||", INV['pre']), INV['init']), LogicExpr_mult("||", pINV)))):
                continue
            else:
                print(LogicExpr("&&", LogicExpr_mult("||", INV['pre']), INV['init']))
                print(LogicExpr_mult("||", pINV))
                exx = False
        
        return exx



            
    
    pre = change(parse_expr_with_meta(pre))
    posts = expr_to_eexpr(parse_expr_with_meta(posts))
    postt = expr_to_eexpr(parse_expr_with_meta(postt))
    r1 = prop(pre, assn, posts, postt)
    ODEL = [parse_hp_with_meta(s) for s in odehps]
    r2 = test(ODEINV, ODEL)
    return r1 and r2     
    
