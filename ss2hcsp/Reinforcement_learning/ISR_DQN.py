import unittest

from ss2hcsp.hcsp.simulator import SimInfo, exec_parallel, graph
from ss2hcsp.hcsp.hcsp import HCSPOutput, HCSPInfo, Procedure, Function
from ss2hcsp.hcsp.parser import parse_module_file
from ss2hcsp.Reinforcement_learning.DQN import DeepQNetwork, DeepQNetworkExternal
import copy

class ISR_Test(unittest.TestCase):
    def run_processes(self, infos: list[HCSPInfo], num_io_events, *, outputs):
        sim_infos = []
        for info in infos:
            procedures = dict()
            functions = dict()
            for proc in info.procedures:
                procedures[proc.name] = proc
            sim_infos.append(SimInfo(info.name, info.hp, procedures=procedures, functions=functions,
                                     outputs=[HCSPOutput(var) for var in outputs]))
        
        network = DeepQNetwork(
            n_actions=4,
            n_features=10 * 9,
            learning_rate=0.01,
            reward_decay=0.9,
            e_greedy_max=1.0,
            e_greedy_min=0.001,
            replace_target_iter=100,
            memory_size=2000,
            e_greedy_decrement=0.997
        )
        network_external = DeepQNetworkExternal(network)
        
        # sum_step = 0
        for _ in range(100):
            s_infos = copy.deepcopy(sim_infos)
            
            res = exec_parallel(s_infos, num_io_events=num_io_events, num_steps=300000,
                                external=network_external)
            p1_value = res['time_series']['P1']
            last_num_step = p1_value[-1]['state']['num_step']
            last_state = p1_value[-1]['state']['success']
            # sum_step += last_num_step
            print(last_num_step)
        
        self.assertTrue(last_state)
        events = [event['str'] for event in res['trace'] if event['str'] not in ('start', 'step')]
        # avg = sum_step/1000
        # print(avg)
        return res, events

    def test_ISRdqn(self):
        with open("ss2hcsp/Reinforcement_learning/ISR_DQN.txt", "r") as f:
            text = f.read()
        infos = parse_module_file(text)
        self.run_processes(infos, 10000000, outputs=['map', 'num_step', 'success'])


if __name__ == "__main__":
    unittest.main()
