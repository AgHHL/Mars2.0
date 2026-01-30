from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar,AConst,RelExpr

class Reference(SL_Block):
    def __init__(self, name, relop, value, sourcetype, st=-1):
        super(Reference, self).__init__('reference',name,1,1,st)
        self.value = value
        self.subsystem_flag = None

        assert relop in ["<=", "<", ">", ">=", "==", "~="]
        self.relop = relop
        self.sourcetype = sourcetype

        assert isinstance(st, (float, int))
        self.st = st

    def get_expr(self):
        if self.relop == '<=':
            self.relop = '>'
        elif self.relop == '<':
            self.relop = '>='
        elif self.relop == '>':
            self.relop = '<='
        elif self.relop == '>=':
            self.relop = '<'
        elif self.relop == '==':
            self.relop = '~='
        elif self.relop == '~=':
            self.relop = '=='
        return self.relop

    def __str__(self):
        return "Reference(%s, %s, in = %s, out = %s, st = %s)" % \
               (self.name, self.value, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_output_hp(self):
        pre_sig = self.dest_lines[0].name
        cur_sig = self.src_lines[0][0].name
        trig_cond = RelExpr(self.relop,AVar(pre_sig),AConst(int(self.value)))
        return hp.ITE([(trig_cond, hp.Assign(cur_sig,AConst(1)))],hp.Assign(cur_sig,AConst(0)))