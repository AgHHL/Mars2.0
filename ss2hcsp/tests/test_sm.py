"""Unit test for sf_convert."""

import unittest
import random
from pstats import Stats
import cProfile

from ss2hcsp.sysml_sm import sm_convert
from ss2hcsp.sysml_sm.parse_copy import SL_Diagram
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import hcsp
from ss2hcsp.tests.simulator_test import run_test as run_simulator_test
from ss2hcsp.tests.sim_test import run_test as run_sim_test
from ss2hcsp.hcsp.pprint import pprint


def run_test(self, filename, num_cycle, res, *, io_filter=None,
             print_chart=False, print_before_simp=False, print_final=False,
             debug_name=False, print_res=False, profile=False, output_to_file=None):
    """Test function for Stateflow diagrams.

    filename : str - name of the XML file.
    num_cycle : int - number of cycles of Stateflow diagram to simulate.
    res : List[str] - expected output events.
    io_filter : str -> bool - (optional) filter for IO events to display.
    print_chart : bool - print parsed chart.
    print_before_simp : bool - print HCSP program before simplification.
    print_final : bool - print HCSP program after optimization.
    debug_name : bool - print size of HCSP program before and after optimization.
    output_to_file : str - (optional) name of file to output HCSP.

    """
    if profile:
        pr = cProfile.Profile()
        pr.enable()

    diagram = SL_Diagram(location=filename)
    proc_map = sm_convert.convert_diagram(
        diagram, print_chart=print_chart, print_before_simp=print_before_simp,
        print_final=print_final, debug_name=debug_name)

    if profile:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    # Optional: output converted HCSP to file
    if output_to_file is not None:
        modules = []
        module_insts = []
        for name, (procs, hp) in proc_map.items():
            procs_lst = [hcsp.Procedure(proc_name, hp) for proc_name, hp in procs.items()]
            modules.append(module.HCSPModule(name, code=hp, procedures=procs_lst))
            module_insts.append(module.HCSPModuleInst(name, name, []))
        system = module.HCSPSystem(module_insts)
        declarations = module.HCSPDeclarations(modules + [system])

        with open(output_to_file, "w") as f:
            f.write(declarations.export())

    # Test result using simulator
    run_simulator_test(self, proc_map, num_cycle, res, io_filter=io_filter,
                       print_res=print_res)

# Path to all test cases
prefix = "./Examples/"

class SFConvertTest(unittest.TestCase):
    def testStates1(self):
        run_test(self, prefix+"syssm/state1_32bit.xml", 3,
            ['log enA', 'log enA1', 'log duA', 'log exA1', 'log enA2', 'delay 0.1',
             'log duA', 'log duA2', 'delay 0.1', 'log duA', 'log duA2', 'delay 0.1'],
            output_to_file=prefix+"syssm/state1_32bit.txt")

    def testStates2(self):
        run_test(self, prefix+"syssm/state2_32bit.xml", 3,
            ['log enA', 'log enA1', 'log exA1', 'log exA', 'log enB', 'log enB1', 'delay 0.1',
             'log duB', 'log duB1', 'delay 0.1', 'log duB', 'log duB1', 'delay 0.1'],
            output_to_file=prefix+"syssm/state2_32bit.txt")

    def testStates4(self):
        run_test(self, prefix+"syssm/state4_32bit.xml", 3,
            ['log enA', 'log enA1', 'log enB', 'log enB1', 'delay 0.1',
             'log enA', 'log enA1', 'delay 0.1', 'log enB', 'log enB1', 'delay 0.1'],
            output_to_file=prefix+"syssm/state4_32bit.txt")

    def testStates7(self):
        run_test(self, prefix+"syssm/state7_32bit.xml", 2,
            ['log enA', 'log enA1', 'log exA1', 'log exA', 'log enA', 'log enA1', 'delay 0.1',
             'log exA1', 'log exA', 'log enA', 'log enA1', 'delay 0.1'],
            output_to_file=prefix+"syssm/state7_32bit.txt")

    def testTransitions1(self):
        run_test(self, prefix+"syssm/transition1_32bit.xml", 1,
            ['log enS', 'log enA', 'log ca', 'log exA', 'log exS', 'log ta',
             'log enT', 'log enB', 'delay 0.1'],
            output_to_file=prefix+"syssm/transition1_32bit.txt")

    def testTransitions2(self):
        run_test(self, prefix+"syssm/transition2_32bit.xml", 2,
            ['log enS', 'log enA', 'log exA', 'log enB', 'delay 0.1',
             'log ca', 'log exB', 'log exS', 'log ta', 'log enT', 'log enB', 'delay 0.1'],
            output_to_file=prefix+"syssm/transition2_32bit.txt")

    def testTransitions4(self):
        run_test(self, prefix+"syssm/transition4_32bit.xml", 2,
            ['log enS', 'log condDefault', 'log tranDefault', 'log enA',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1'],
            output_to_file=prefix+"syssm/transition4_32bit.txt")

    def testJunctions1(self):
        run_test(self, prefix+"syssm/junction1_32bit.xml", 1,
            ['log enA', 'log enD', 'delay 0.1'],
            output_to_file=prefix+"syssm/junction1_32bit.txt")

    def testJunctions2(self):
        run_test(self, prefix+"syssm/junction2_32bit.xml", 2,
            ['log enA', 'log exA', 'log enB', 'delay 0.1', 'log conBJun', 'log conJunC',
             'log exB', 'log tranBJun', 'log tranJunC', 'log enC', 'delay 0.1'],
            output_to_file=prefix+"syssm/junction2_32bit.txt")

    def testJunctions4(self):
        run_test(self, prefix+"syssm/junction4_32bit.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log c1', 'log c2', 'log exA1', 'log exA',
             'log t1', 'log t2', 'log enC', 'log enC2', 'delay 0.1'],
            output_to_file=prefix+"syssm/junction4_32bit.txt")

    def testJunctions5(self):
        run_test(self, prefix+"syssm/junction5_32bit.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log ca', 'log exA1', 'log enA2', 'delay 0.1'],
            output_to_file=prefix+"syssm/junction5_32bit.txt")

    def testJunctions6(self):
        run_test(self, prefix+"syssm/junction6_32bit.xml", 1,
            ['log enA', 'log ca', 'log ca', 'log exA', 'log ta2', 'log ta4',
             'log enC', 'delay 0.1'],
            output_to_file=prefix+"syssm/junction6_32bit.txt")

    def testJunctions7(self):
        run_test(self, prefix+"syssm/junction7_32bit.xml", 1,
            ['log enA', 'log exA', 'log xle2', 'log yeq2', 'log zge2', 'log enC', 'delay 0.1'],
            output_to_file=prefix+"syssm/junction7_32bit.txt")

    def testEarlyReturn1(self):
        run_test(self, prefix+"syssm/EarlyReturn1_32bit.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"syssm/EarlyReturn1_32bit.txt")

    def testEarlyReturn2(self):
        run_test(self, prefix+"syssm/EarlyReturn2_32bit.xml", 1,
            ['log en_A', 'log en_A1', 'log E', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"syssm/EarlyReturn2_32bit.txt")

    def testEarlyReturn3(self):
        run_test(self, prefix+"syssm/EarlyReturn3_32bit.xml", 1,
            ['log en_A 1', 'log ex_A 2', 'log en_C 2', 'delay 0.1'],
            output_to_file=prefix+"syssm/EarlyReturn3_32bit.txt")

    def testEarlyReturn4(self):
        run_test(self, prefix+"syssm/EarlyReturn4_32bit.xml", 1,
            ['log ca', 'log ta', 'log en_A2', 'delay 0.1'],
            output_to_file=prefix+"syssm/EarlyReturn4_32bit.txt")

    def testContinuous1(self):
        run_test(self, prefix+"syssm/continuous1_32bit.xml", 2,
            ['log enA 0.000 0.000', 'delay 0.5',
             'log conAB1 1.000 0.500', 'log exA 1.000 0.500', 'log tranAB1 1.000 0.500',
             'log enB 1.000 0.500', 'log enB1 0.000 0.500', 'delay 1.0'],
            output_to_file=prefix+"syssm/continuous1_32bit.txt")

    def testContinuous2(self):
        run_test(self, prefix+"syssm/continuous2_32bit.xml", 3,
            ['log enA 0.000 1.000', 'delay 0.524', 'delay 0.0',
             'log conAB1 0.500 0.866', 'log exA 0.500 0.866', 'log tranAB1 0.500 0.866',
             'log enB 0.500 0.866', 'log enB1 0.000 0.866', 'delay 1.0'],
            output_to_file=prefix+"syssm/continuous2_32bit.txt")

    def testContinuous3(self):
        run_test(self, prefix+"syssm/continuous3_32bit.xml", 2,
            ['log enA 0.000 0.000', 'delay 1.414',
             'log conAB1 1.414 1.000', 'log exA 1.414 1.000', 'log tranAB1 1.414 1.000',
             'log enB 1.414 1.000', 'log enB1 0.000 1.000', 'delay 1.0'],
            output_to_file=prefix+"syssm/continuous3_32bit.txt")

    def testContinuous4(self):
        run_test(self, prefix+"syssm/continuous4_32bit.xml", 2,
            ['log enA 0.000 0.000', 'delay 1.0',
             'log conAB 1.000 0.500', 'log exA 1.000 0.500', 'log tranAB 1.000 0.500',
             'log enB 1.000 0.500', 'log enB1 0.000 0.500', 'delay 1.0'],
            output_to_file=prefix+"syssm/continuous4_32bit.txt")

    def testContinuous5(self):
        run_test(self, prefix+"syssm/continuous5_32bit.xml", 3,
            ['log enA', 'log enA1', 'delay 1.0', 'log enA2', 'delay 1.0',
             'log exA', 'log enB', 'delay 1.0'],
            output_to_file=prefix+"syssm/continuous5_32bit.txt")

    def testContinuous6(self):
        run_test(self, prefix+"syssm/continuous6_32bit.xml", 3,
            ['log enA', 'log enA1', 'delay 1.0', 'log enA2', 'delay 0.5',
             'log condA2B', 'log exA', 'log enB', 'delay 1.0'],
            output_to_file=prefix+"syssm/continuous6_32bit.txt")

    def testEvent1(self):
        run_test(self, prefix+"syssm/event1_32bit.xml", 1,
            ['log b', 'log a', 'log en_A2', 'log tb', 'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"syssm/event1_32bit.txt")

    def testEvent2(self):
        run_test(self, prefix+"syssm/event2_32bit.xml", 1,
            ['log b', 'log a', 'log en_A2', 'log c', 'log en_C2', 'log tb',
             'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"syssm/event2_32bit.txt")

    def testEvent5(self):
        run_test(self, prefix+"syssm/event5_32bit.xml", 1,
            ['log en_A2', 'log b', 'log en_A3', 'log tb', 'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"syssm/event5_32bit.txt")

    def testEvent6(self):
        run_test(self, prefix+"syssm/event6_32bit.xml", 1,
            ['log a 5', 'log a 4', 'log a 3', 'log a 2', 'log a 1', 'log a 0',
             'log en_B2 0', 'delay 0.1'],
            output_to_file=prefix+"syssm/event6_32bit.txt")

if __name__ == "__main__":
    unittest.main()
