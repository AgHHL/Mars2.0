from typing import Optional

from ss2hcsp.hcsp.expr import Expr
from ss2hcsp.hcsp.label import Label

class Assertion:
    """Base class ."""
    def __init__(self):
        pass

class OrdinaryAssertion(Assertion):
    """Represents an assertion with its expression and proof methods.

    Attributes
    ----------
    expr : Expr
        assertion expression
    proof_methods : ProofMethods
        methods used for proof. 

    Both loop invariant with proof methods and postcondition with proof methods are
    instances of OrdinaryAssertion.

    """
    def __init__(self, expr: Expr, proof_methods: "ProofMethods", meta=None):
        super(OrdinaryAssertion, self).__init__()
        assert isinstance(expr, Expr)
        assert isinstance(proof_methods, ProofMethods)
        self.meta = meta
        self.expr = expr
        self.proof_methods = proof_methods


class CutInvariant(Assertion):
    def __init__(self, expr, proof_methods, rule = None, rule_arg=None, meta=None):
        super(CutInvariant, self).__init__()
        assert isinstance(expr, Expr)
        assert isinstance(proof_methods, ProofMethods)
        if rule:
            assert isinstance(rule, str)
        if rule_arg:
            assert isinstance(rule_arg, Expr)
        self.meta = meta
        self.expr = expr
        self.proof_methods = proof_methods
        self.rule = rule
        self.rule_arg = rule_arg

class GhostIntro(Assertion):
    """Introduces a ghost variable."""
    def __init__(self, var: str, diff: Expr, meta=None):
        super(GhostIntro, self).__init__()
        assert isinstance(diff, Expr)
        self.meta = meta
        self.var = str(var)
        self.diff = diff


class ProofMethod:
    """Represents the label and corresponding proof method.

    Attributes
    ----------
    method : str
        name of the backend prover, e.g. "z3" or "wolfram"
    label : Optional[str], default to None
        e.g. "1.1"

    """
    def __init__(self, method: str, label: Optional[Label]=None, meta=None):
        self.meta = meta
        # label can be None
        if label:
            assert isinstance(label, Label)
        assert isinstance(method, str)
        self.label = label
        self.method = method

    def __str__(self):
        if self.label:
            return str(self.label) + ': ' + self.method
        else:
            return self.method

class ProofMethods:
    """Represents a list of ProofMethod objets.
    
    Attributes
    ----------
    pms : tuple[ProofMethod]

    """
    def __init__(self, *pms: ProofMethod, meta=None):
        assert all(isinstance(pm, ProofMethod) for pm in pms)
        self.pms = tuple(pms)
        self.meta = meta
