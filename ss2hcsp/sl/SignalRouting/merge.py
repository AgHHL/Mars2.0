from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, RelExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class Merge(SL_Block):
    """Switch of two dest lines."""
    def __init__(self, name, num_src, num_dest, init_value, st=-1):
        super(Merge, self).__init__("merge", name, num_src, num_dest, st)

        assert isinstance(init_value, int)
        self.init_value = init_value

    def __str__(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Merge(%s, %s, in = %s, out = %s, st = %s)" % \
            (self.name, self.init_value, str(self.dest_lines), str(self.src_lines), self.st)

    def get_output_hp(self):
        output_list = []
        cur_sig = self.src_lines[0][0].name
        for block in self.dest_lines:
            port = block.src_port
            out_var = block.name
            merge_cond = RelExpr('==', AVar(out_var), AConst(int(1)))
            output_list.append(hp.ITE([(merge_cond, hp.Assign(cur_sig,AVar(out_var +'_'+str(port))))]))
        return hp.seq(output_list)
