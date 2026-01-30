"""Modules for hybrid programs"""

import os
from typing import Iterable, Union

from ss2hcsp.hcsp.hcsp import HCSPInfo, HCSPOutput, Procedure, HCSP, Channel
from ss2hcsp.hcsp import pprint
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import Expr


class ModuleException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


class HCSPModule:
    """Template for an HCSP process.

    Attributes
    ----------
    name: str
        name of the module.
    code: HCSP
        code (template) for the main process.
    params: tuple[str]
        list of parameters that can be substituted for channel names
        and variables in the module.
    outputs: tuple[HCSPOutput]
        list of output variables.
    procedures: tuple[Procedure]
        list of declared procedures.
    
    """
    def __init__(self, name: str, code: HCSP, *,
                 params: Iterable[str] = tuple(),
                 outputs: Iterable[HCSPOutput] = tuple(),
                 procedures: Iterable[Procedure] = tuple(),
                 meta=None):
        self.name = name
        self.code = code
        self.params = tuple(params)
        self.outputs = tuple(outputs)
        self.procedures = tuple(procedures)
        self.meta = meta

    def __eq__(self, other):
        return isinstance(other, HCSPModule) and self.name == other.name and \
            self.params == other.params and self.outputs == other.outputs and \
            self.procedures == other.procedures and self.code == other.code

    def __str__(self):
        return self.name + '(' + ','.join(self.params) + ')'

    def __repr__(self):
        if self.params:
            return "Module(%s,%s)" % (self.name, ','.join(self.params))
        else:
            return "Module(%s)" % self.name

    def export(self):
        """Print the string that will parse to the module."""
        def str_of_outputs(outputs: tuple[str]):
            if outputs:
                return "output %s;\n" % (', '.join(str(output) for output in outputs))
            else:
                return ""

        def str_of_procedure(procedures: tuple[Procedure]):
            res = ""
            for procedure in procedures:
                res += "procedure %s begin\n" % procedure.name
                body = pprint.pprint(procedure.hp)
                for line in body.split('\n'):
                    res += "  " + line + "\n"
                res += "end\n\n"
            return res

        def str_of_code(code):
            res = ""
            code_str = pprint.pprint(code)
            for line in code_str.split('\n'):
                res += "  " + line + "\n"
            return res

        res = "module %s(%s):\n%s%sbegin\n%send\nendmodule" % (
            self.name,
            ','.join(self.params),
            str_of_outputs(self.outputs),
            str_of_procedure(self.procedures),
            str_of_code(self.code)
        )
        return res


class HCSPModuleInst:
    """An instantiation of an HCSP module.

    Maintains name of the resulting process, name of the HCSP module
    to be instantiated, and list of concrete argments for the parameters.

    Attributes
    ----------
    name: str
        name of the instantiated HCSP process
    module_name: str
        name of the module before instantiation
    args: tuple[Expr | Channel]
        list of arguments, in the same order as module declaration. Each
        argument is either an expression or a channel

    """
    def __init__(self, name: str, module_name: str,
                 args: Iterable[Union[Expr , Channel]] = tuple(), meta=None):
        self.name: str = name
        self.module_name: str = module_name
        self.args: tuple[Expr | Channel] = tuple(args)
        self.meta = meta

    def __str__(self):
        if self.name == self.module_name:
            return "%s(%s)" % (self.module_name, ','.join(str(arg) for arg in self.args))
        else:
            return "%s=%s(%s)" % (self.name, self.module_name,
                ','.join(str(arg) for arg in self.args))

    def __repr__(self):
        if self.args:
            return "ModuleInst(%s,%s)" % (self.name, self.module_name)
        else:
            return "ModuleInst(%s,%s,%s)" % (self.name, self.module_name,
                ','.join(str(arg) for arg in self.args))

    def export(self) -> str:
        """Print the string that will parse to the module instantiation."""
        def print_arg(arg):
            if isinstance(arg, expr.AConst):
                if isinstance(arg.value, str) and arg.value[0] != "\"":
                    return "$\"" + arg.value + "\""
                else:
                    return "$" + str(arg.value)
            else:
                return str(arg)

        if self.name == self.module_name:
            return "%s(%s)" % (self.name,
                ', '.join(print_arg(arg) for arg in self.args))
        else:
            return "%s = %s(%s)" % (self.name, self.module_name,
                ', '.join(print_arg(arg) for arg in self.args))

    def generate_inst(self, module: HCSPModule) -> HCSPInfo:
        """Given the module, construct the corresponding HCSP info."""

        # First, construct the mapping between formal and actual parameters
        inst: dict[str, Union[Expr , Channel]] = dict()
        if len(module.params) != len(self.args):
            raise ModuleException(
                f"Number of arguments for {self.name} does not match: "
                f"{len(module.params)} vs {len(self.args)}"
            )
        for param, arg in zip(module.params, self.args):
            inst[param] = arg

        # Next, instantiate code and each procedure
        code = module.code.subst_comm(inst)
        procedures = [Procedure(proc.name, proc.hp.subst_comm(inst)) for proc in module.procedures]
        
        return HCSPInfo(self.name, code, outputs=module.outputs, procedures=procedures)


class HCSPSystem:
    """An HCSP system keeps a list of module instantiations.
    
    This class keeps sufficient information to reconstruct the parallel
    HCSP process.
    
    Attributes
    ----------
    module_insts: tuple[HCSPModuleInst]
        list of module instantiations

    """
    def __init__(self, module_insts: Iterable[HCSPModuleInst], meta=None):
        self.module_insts = tuple(module_insts)
        self.meta = meta

    def __str__(self):
        return ' ||\n'.join(module_inst.export() for module_inst in self.module_insts)

    def __repr__(self):
        return "System(%s)" % ("; ".join(str(module_inst) for module_inst in self.module_insts))


hcsp_import_path: list[str] = [
    './ss2hcsp/common',
]

# Read additional import path from import_path.txt
try:
    hcsp_import_path = [os.path.abspath(path) for path in hcsp_import_path]
    with open('./ss2hcsp/import_path.txt') as f:
        for line in f.readlines():
            hcsp_import_path.append(os.path.abspath(line.strip()))
except FileNotFoundError:
    print('Warning: import_path.txt not found.')

def read_file(filename: str) -> str:
    """Given file name, attempt to locate the file in the import paths
    in reverse order. Returns the content of the file. If the file is not
    found, return None.

    """
    for path in reversed(hcsp_import_path):
        try:
            with open(os.path.join(path, filename), encoding='utf-8') as f:
                text = f.read()
            return text
        except FileNotFoundError:
            pass
        
    return None


class HCSPDeclarations:
    """A list of HCSP declarations.

    Contains a number of module declarations (HCSPModule) and a single
    system declaration (HCSPSystem).

    """
    def __init__(self, args: list[Union[HCSPModule, HCSPSystem, "HCSPDeclarations"]], meta=None):
        """Input is a list of HCSPModule, HCSPSystem, or HCSPDeclaration objects.
        Modules in the HCSPDeclarations are included in the current declaration.
        
        There should be exactly one HCSPSystem in `args`.

        """
        # Mapping from module name to HCSPModule
        self.modules: dict[str, HCSPModule] = dict()

        # Overall system
        self.system: HCSPSystem = None

        for arg in args:
            if isinstance(arg, HCSPModule):
                if arg.name in self.modules:
                    raise ModuleException(f"Module name {arg.name} is repeated")
                self.modules[arg.name] = arg
            elif isinstance(arg, HCSPSystem):
                if self.system is not None:
                    raise ModuleException("More than one system in declaration")
                self.system = arg
            elif isinstance(arg, HCSPDeclarations):
                for name in arg.modules:
                    if name in self.modules:
                        raise ModuleException(f"Import name {name} is repeated")
                    self.modules[name] = arg.modules[name]
            else:
                raise NotImplementedError(f"HCSPDeclaration: input {arg} of type {type(arg)}")
        self.meta = meta

    def __str__(self):
        res = ""
        for name in sorted(self.modules.keys()):
            res += str(self.modules[name]) + '\n'
        res += str(self.system)
        return res

    def __repr__(self):
        res = "Decls(\n"
        for name in sorted(self.modules.keys()):
            res += '  ' + repr(self.modules[name]) + '\n'
        res += '  ' + repr(self.system) + '\n)'
        return res

    def export(self) -> str:
        """Convert declarations to string that can be written to a file."""
        res = "%type: module\n\n"
        for _, module in self.modules.items():
            res += module.export() + "\n\n"
        res += "system\n" + str(self.system) + "\nendsystem\n"
        return res

    def generateHCSPInfo(self) -> list[HCSPInfo]:
        """Produce list of HCSPInfo objects."""
        if self.system is None:
            raise ModuleException("No system in declaration")

        infos = []
        for module_inst in self.system.module_insts:
            if module_inst.module_name not in self.modules:
                raise ModuleException(
                    "generateHCSPInfo: %s not found in declaration" % module_inst.module_name)

            module = self.modules[module_inst.module_name]
            hcsp_info = module_inst.generate_inst(module)
            infos.append(hcsp_info)

        return infos
