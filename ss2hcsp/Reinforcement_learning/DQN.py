import torch
import torch.nn as nn
import numpy as np
from torch import Tensor
import torch.nn.functional as F
import ast

from ss2hcsp.hcsp.simulator import SimulatorExternal

np.random.seed(42)
torch.manual_seed(2)

class Network(nn.Module):
    """Fully-connected network with three hidden layers and one output layer.

    Input layer has size `n_features` and output layer has size `n_actions`.
    The three hidden layers have sizes 128, 128, 64, respectively.

    """
    def __init__(self, n_features: int, n_actions: int):
        super(Network, self).__init__()
        self.n_features = n_features

        self.fc1 = nn.Linear(self.n_features, 128)
        self.fc1.weight.data.normal_(0, 0.1)
        
        self.fc2 = nn.Linear(128, 128)
        self.fc2.weight.data.normal_(0, 0.1)
        
        self.fc3 = nn.Linear(128, 64)
        self.fc3.weight.data.normal_(0, 0.1)
        
        self.fc4 = nn.Linear(64, n_actions)
        self.fc4.weight.data.normal_(0, 0.1)

    def forward(self, s: Tensor):
        s = self.fc1(s)
        s = F.relu(s)
        s = self.fc2(s)
        s = F.relu(s)
        s = self.fc3(s)
        s = F.relu(s)
        q = self.fc4(s)
        return q


class DeepQNetwork(nn.Module):
    """Implementation of Deep Q-Network (DQN)."""
    def __init__(self,
                 n_actions: int,
                 n_features: int,
                 learning_rate=0.01,
                 reward_decay=0.9,
                 e_greedy_max=0.9,
                 e_greedy_min=0.1,
                 replace_target_iter=300,
                 memory_size=500,
                 batch_size=32,
                 e_greedy_decrement=None):
        super(DeepQNetwork, self).__init__()

        self.n_actions = n_actions
        self.n_features = n_features
        self.learning_rate = learning_rate
        self.gamma = reward_decay
        self.epsilon_max = e_greedy_max
        self.epsilon_min = e_greedy_min
        self.replace_target_iter = replace_target_iter
        self.memory_size = memory_size
        self.batch_size = batch_size
        self.epsilon_decrement = e_greedy_decrement
        self.epsilon = self.epsilon_max if e_greedy_decrement is not None else self.epsilon_min
        self.global_step = 0
        self.learn_step_counter = 0

        self.memory = list(np.zeros((memory_size, 4)))

        self.eval_net = Network(n_features=self.n_features, n_actions=self.n_actions)
        self.target_net = Network(n_features=self.n_features, n_actions=self.n_actions)
        self.loss_function = nn.MSELoss()
        self.optimizer = torch.optim.Adam(self.eval_net.parameters(), lr=self.learning_rate)

    def store_transition(self, s, a, r, s_):
        """Stores a single transition (experience) in replay memory.
        
        s - the current state
        a - action taken in the current state
        r - reward received after taking the action
        s_ - the next state observed after taking the action

        """
        if not hasattr(self, 'memory_counter'):
            self.memory_counter = 0

        s = np.asarray(s).flatten()
        s_ = np.asarray(s_).flatten()
        a = np.array([a])
        index = self.memory_counter % self.memory_size
        self.memory[index] = [s, a, r, s_]

        self.memory_counter += 1

    def choose_action(self, partial_observation, observation):
        """Selects an action based on the current state using an
        epsilon-greedy policy:

        - with probability epsilon: choose the action with highest Q-value.
        - otherwise, choose a random action.
        
        """
        
        if np.random.uniform() < self.epsilon:
            action = np.random.randint(0, self.n_actions)
            for i in range(len(partial_observation)):
                if partial_observation[i] == 1:
                    while partial_observation[action] == 1:
                        action = np.random.randint(0, self.n_actions)
        else:
            s = torch.FloatTensor(np.asarray(observation).flatten())
            actions_value: Tensor = self.eval_net(s)
            action = np.argmax(actions_value.detach().numpy())

            for i in range(len(partial_observation)):
                if partial_observation[i] == 1:
                    while partial_observation[action] == 1:
                        action = np.random.randint(0, self.n_actions)


        return action
    
    def get_global_step(self):
        self.global_step += 1
        return self.global_step


    def learn(self):
        """Update network using a sampling of experiences from replay memory."""

        # Periodically update the target network with the evaluation network
        if self.learn_step_counter % self.replace_target_iter == 0:
            self.target_net.load_state_dict(self.eval_net.state_dict())

        # Sample mini-batch from replay memory
        if self.memory_counter > self.memory_size:
            sample_index = np.random.choice(self.memory_size, size=self.batch_size)
        else:
            sample_index = np.random.choice(self.memory_counter, size=self.batch_size)

        b_s = []
        b_a = []
        b_r = []
        b_s_ = []
        for i in sample_index:
            b_s.append(self.memory[i][0])
            b_a.append(np.array(self.memory[i][1], dtype=np.int32))
            b_r.append(np.array([self.memory[i][2]], dtype=np.int32))
            b_s_.append(self.memory[i][3])

        b_s = torch.FloatTensor(np.stack(b_s))
        b_a = torch.LongTensor(np.stack(b_a))
        b_r = torch.FloatTensor(np.stack(b_r))
        b_s_ = torch.FloatTensor(np.stack(b_s_))

        # Compute predicted Q-value (q_eval) and next Q-values (q_next)
        q_eval = self.eval_net(b_s).gather(1, b_a)
        q_next = self.target_net(b_s_).detach()

        # Target Q-value equals immediate reward plus discounted value of next state
        q_target = b_r + self.gamma * q_next.max(1)[0].unsqueeze(1)

        # Compute loss and update weights
        loss = self.loss_function(q_eval, q_target)
        self.optimizer.zero_grad()
        loss.backward()
        self.optimizer.step()
        # print(f"Step: {self.learn_step_counter}, Epsilon: {self.epsilon}")
        # Update epsilon: the exploration rate epsilon is increased over time,
        # until reaching epsilon_max
        if self.epsilon > self.epsilon_min:
            self.epsilon *= self.epsilon_decrement
        else:
            self.epsilon = self.epsilon_min
        
        self.learn_step_counter += 1

    def get_fullmap(self, map_code):
        """
        Retrieve the corresponding map name based on the map_code and load the map file.

        Parameters:
            map_code (int): Map code, where 1 represents ISR map, 2 represents MIT map, and 3 represents Pentagon map.

        Returns:
            list: The generated 2D array representing the map.
        """

        # Define the mapping between map codes and map names
        map_name_dict = {
            1: "ISR",
            2: "MIT",
            3: "Pentagon"
        }

        # Retrieve the map name
        if map_code not in map_name_dict:
            raise ValueError(f"Error: Invalid map code {map_code}.")

        map_name = map_name_dict[map_code]

        # Define the file path
        file_path = f"ss2hcsp/Reinforcement_learning/map/{map_name}.txt"

        try:
            # Read the file content
            with open(file_path, "r") as file:
                content = file.read()

            # Parse the file content into a Python object (a 2D list in this case)
            mmap = ast.literal_eval(content)

            # Return the generated 2D array
            return mmap
        except FileNotFoundError:
            print(f"Error: File '{file_path}' does not exist.")
            return None
        except SyntaxError:
            print(f"Error: File '{file_path}' contains invalid syntax.")
            return None
    
    def init_agent(self, x, y, current_state):
        """
            Initialize a 2D array of size x rows and y columns, where all elements are 0,
        except for the element at the current_state coordinates, which is set to 1.
        """
        map = [[0 for _ in range(y)] for _ in range(x)]

        row, col = current_state
        map[row][col] = 1

        return map

class DeepQNetworkExternal(SimulatorExternal):
    def __init__(self, network: DeepQNetwork):
        self.name = "DeepQNetwork"
        self.operations = ("choose_action", "store_transition", "learn", "get_fullmap", "init_agent", "get_global_step")
        self.network = network
    
    def exec(self, operation_name: str, args: list):
        if operation_name == "choose_action":
            assert len(args) == 2
            partial_observation, observation = args
            return self.network.choose_action(partial_observation, observation)
        elif operation_name == "store_transition":
            assert len(args) == 4
            s, a, r, s_ = args
            self.network.store_transition(s, a, r, s_)
            return
        elif operation_name == "learn":
            assert len(args) == 0
            self.network.learn()
            return
        elif operation_name == "get_fullmap":
            assert len(args) == 1
            map_code = args[0]
            return self.network.get_fullmap(map_code)
        elif operation_name == "init_agent":
            assert len(args) == 3
            x, y, current_state = args
            return self.network.init_agent(x, y, current_state)
        elif operation_name == "get_global_step":
            assert len(args) == 0 
            return self.network.get_global_step()
        else:
            raise NotImplementedError(f"DeepQNetwork: unsupported operation {operation_name}")
