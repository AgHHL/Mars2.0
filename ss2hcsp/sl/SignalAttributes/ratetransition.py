from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, true_expr, OpExpr, RelExpr
import ss2hcsp.hcsp.hcsp as hp

class RateTransition(SL_Block):
    def __init__(self, name, InitialCondition, st):
        super(RateTransition, self).__init__("ratetransition", name, 1, 1, st)

        assert isinstance(st, (int, float))
        self.st = st
        self.init_value = InitialCondition

    def __str__(self):
        in_var = self.dest_lines[0].name
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s (st = %s)" % (self.name, out_var, in_var, self.st)

    def __repr__(self):
        return "RateTransition(%s, %s, in = %s, out = %s, st = %s)" % \
            (self.name, self.init_value, str(self.dest_lines), str(self.src_lines), self.st)

    def get_output_hp(self):
        out_var = self.src_lines[0][0].name
        in_var = self.dest_lines[0].name
        return hp.Assign(out_var, AVar(in_var))

