import torch
import torch.nn as nn
import numpy as np
from torch import Tensor
import torch.nn.functional as F
import ast

from ss2hcsp.hcsp.simulator import SimulatorExternal

np.random.seed(42)
torch.manual_seed(2)
class CNNNetwork(nn.Module):
    """Convolutional neural network for processing grid-based states."""
    def __init__(self, n_actions: int, grid_size: tuple):
        super(CNNNetwork, self).__init__()
        self.grid_size = grid_size  # (height, width) of the grid
        self.n_actions = n_actions

        # Convolutional layers
        self.conv1 = nn.Conv2d(in_channels=1, out_channels=16, kernel_size=3, stride=1, padding=1)
        self.conv2 = nn.Conv2d(in_channels=16, out_channels=32, kernel_size=3, stride=1, padding=1)
        self.conv3 = nn.Conv2d(in_channels=32, out_channels=64, kernel_size=3, stride=1, padding=1)

        # Fully connected layers
        self.fc1 = nn.Linear(64 * self.grid_size[0] * self.grid_size[1], 128)
        self.fc2 = nn.Linear(128, self.n_actions)

    def forward(self, s: Tensor):
        # Reshape input to (batch_size, channels, height, width)
        s = s.view(-1, 1, self.grid_size[0], self.grid_size[1])

        # Convolutional layers with ReLU activation
        s = F.relu(self.conv1(s))
        s = F.relu(self.conv2(s))
        s = F.relu(self.conv3(s))

        # Flatten the output for fully connected layers
        s = s.view(-1, 64 * self.grid_size[0] * self.grid_size[1])

        # Fully connected layers
        s = F.relu(self.fc1(s))
        q = self.fc2(s)

        return q

# class CNNNetwork(nn.Module):
#     """Convolutional neural network for processing grid-based states."""
#     def __init__(self, n_actions: int, grid_size: tuple):
#         super(CNNNetwork, self).__init__()
#         self.grid_size = grid_size  # (height, width) of the grid
#         self.n_actions = n_actions

#         # Convolutional layers
#         self.conv1 = nn.Conv2d(in_channels=1, out_channels=8, kernel_size=3, stride=1, padding=1)
#         self.conv2 = nn.Conv2d(in_channels=8, out_channels=16, kernel_size=3, stride=1, padding=1)
#         self.conv3 = nn.Conv2d(in_channels=16, out_channels=32, kernel_size=3, stride=1, padding=1)

#         # Fully connected layers
#         self.fc1 = nn.Linear(32 * self.grid_size[0] * self.grid_size[1], 128)
#         self.fc2 = nn.Linear(128, self.n_actions)

#     def forward(self, s: Tensor):
#         # Reshape input to (batch_size, channels, height, width)
#         s = s.view(-1, 1, self.grid_size[0], self.grid_size[1])

#         # Convolutional layers with ReLU activation
#         s = F.relu(self.conv1(s))  # Output shape: (batch_size, 8, height, width)
#         s = F.relu(self.conv2(s))  # Output shape: (batch_size, 16, height, width)
#         s = F.relu(self.conv3(s))  # Output shape: (batch_size, 32, height, width)

#         # Flatten the output for fully connected layers
#         s = s.view(-1, 32 * self.grid_size[0] * self.grid_size[1])  # 注意：32 是最后一个卷积层的输出通道数

#         # Fully connected layers
#         s = F.relu(self.fc1(s))
#         q = self.fc2(s)

#         return q

class MultiAgentDeepQNetwork(nn.Module):
    """Implementation of Deep Q-Network (DQN) for two agents using CNN."""
    def __init__(self,
                 n_actions: int,
                 grid_size: tuple,  # (height, width) of the grid
                 learning_rate=0.01,
                 reward_decay=0.9,
                 e_greedy=0.9,
                 replace_target_iter=300,
                 memory_size=500,
                 batch_size=32,
                 e_greedy_increment=None):
        super(MultiAgentDeepQNetwork, self).__init__()

        self.n_actions = n_actions
        self.grid_size = grid_size  # 确保 grid_size 是元组
        self.learning_rate = learning_rate
        self.gamma = reward_decay
        self.epsilon_max = e_greedy
        self.replace_target_iter = replace_target_iter
        self.memory_size = memory_size
        self.batch_size = batch_size
        self.epsilon_increment = e_greedy_increment
        self.epsilon = 0 if e_greedy_increment is not None else self.epsilon_max
        self.learn_step_counter = 0

        # Initialize memory for both agents
        self.memory_1 = list(np.zeros((memory_size, 4)))  # Memory for agent 1
        self.memory_2 = list(np.zeros((memory_size, 4)))  # Memory for agent 2
        self.memory_counter_1 = 0
        self.memory_counter_2 = 0

        # Initialize CNN networks for both agents
        self.eval_net_1 = CNNNetwork(n_actions=self.n_actions, grid_size=self.grid_size)
        self.target_net_1 = CNNNetwork(n_actions=self.n_actions, grid_size=self.grid_size)
        self.eval_net_2 = CNNNetwork(n_actions=self.n_actions, grid_size=self.grid_size)
        self.target_net_2 = CNNNetwork(n_actions=self.n_actions, grid_size=self.grid_size)

        self.optimizer_1 = torch.optim.Adam(self.eval_net_1.parameters(), lr=self.learning_rate)
        self.optimizer_2 = torch.optim.Adam(self.eval_net_2.parameters(), lr=self.learning_rate)
        self.loss_function = nn.MSELoss()

    def store_transition(self, agent_id: int, s, a, r, s_):
        """Stores a single transition (experience) in replay memory for a specific agent."""
        s = np.asarray(s).flatten()
        s_ = np.asarray(s_).flatten()
        a = np.array([a])
        if agent_id == 1:
            index = self.memory_counter_1 % self.memory_size
            self.memory_1[index] = [s, a, r, s_]
            self.memory_counter_1 += 1
        elif agent_id == 2:
            index = self.memory_counter_2 % self.memory_size
            self.memory_2[index] = [s, a, r, s_]
            self.memory_counter_2 += 1

    def choose_action(self, agent_id: int, partial_observation, observation):
        """Selects an action for a specific agent based on the current state using an epsilon-greedy policy."""
        if np.random.uniform() < self.epsilon:
            s = torch.FloatTensor(np.asarray(observation).reshape(self.grid_size))
            if agent_id == 1:
                actions_value: Tensor = self.eval_net_1(s)
            elif agent_id == 2:
                actions_value: Tensor = self.eval_net_2(s)
            action = np.argmax(actions_value.detach().numpy())

            for i in range(len(partial_observation)):
                if partial_observation[i] == 1:
                    while partial_observation[action] == 1:
                        action = np.random.randint(0, self.n_actions)
        else:
            action = np.random.randint(0, self.n_actions)
            for i in range(len(partial_observation)):
                if partial_observation[i] == 1:
                    while partial_observation[action] == 1:
                        action = np.random.randint(0, self.n_actions)

        return action

    def learn(self, agent_id: int):
        """Update network for a specific agent using a sampling of experiences from replay memory."""
        if self.learn_step_counter % self.replace_target_iter == 0:
            if agent_id == 1:
                self.target_net_1.load_state_dict(self.eval_net_1.state_dict())
            elif agent_id == 2:
                self.target_net_2.load_state_dict(self.eval_net_2.state_dict())

        if agent_id == 1:
            memory = self.memory_1
            memory_counter = self.memory_counter_1
            eval_net = self.eval_net_1
            target_net = self.target_net_1
            optimizer = self.optimizer_1
        elif agent_id == 2:
            memory = self.memory_2
            memory_counter = self.memory_counter_2
            eval_net = self.eval_net_2
            target_net = self.target_net_2
            optimizer = self.optimizer_2

        if memory_counter > self.memory_size:
            sample_index = np.random.choice(self.memory_size, size=self.batch_size)
        else:
            sample_index = np.random.choice(memory_counter, size=self.batch_size)

        b_s = []
        b_a = []
        b_r = []
        b_s_ = []
        for i in sample_index:
            b_s.append(memory[i][0])
            b_a.append(np.array(memory[i][1], dtype=np.int32))
            b_r.append(np.array([memory[i][2]], dtype=np.int32))
            b_s_.append(memory[i][3])

        b_s = torch.FloatTensor(b_s).view(-1, self.grid_size[0], self.grid_size[1])
        b_a = torch.LongTensor(b_a)
        b_r = torch.FloatTensor(b_r)
        b_s_ = torch.FloatTensor(b_s_).view(-1, self.grid_size[0], self.grid_size[1])

        q_eval = eval_net(b_s).gather(1, b_a)
        q_next = target_net(b_s_).detach()
        q_target = b_r + self.gamma * q_next.max(1)[0]

        loss = self.loss_function(q_eval, q_target)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        if self.epsilon < self.epsilon_max:
            self.epsilon = self.epsilon + self.epsilon_increment
        else:
            self.epsilon = self.epsilon_max
        self.learn_step_counter += 1

    def get_fullmap(self, map_code):
        """Retrieve the corresponding map based on the map_code."""
        map_name_dict = {1: "MAISR", 2: "MAMIT", 3: "MAPentagon"}
        if map_code not in map_name_dict:
            raise ValueError(f"Error: Invalid map code {map_code}.")

        map_name = map_name_dict[map_code]
        file_path = f"ss2hcsp/Reinforcement_learning/map/{map_name}.txt"

        try:
            with open(file_path, "r") as file:
                content = file.read()
            mmap = ast.literal_eval(content)
            return mmap
        except FileNotFoundError:
            print(f"Error: File '{file_path}' does not exist.")
            return None
        except SyntaxError:
            print(f"Error: File '{file_path}' contains invalid syntax.")
            return None

    def init_agent1(self, x, y, current_state_1):
        """Initialize a 2D array for an agent."""
        map1 = [[0 for _ in range(y)] for _ in range(x)]

        row_1, col_1 = current_state_1
        map1[row_1][col_1] = 1

        return map1
    
    def init_agent2(self, x, y, current_state_2):
        """Initialize a 2D array for an agent."""
        map2 = [[0 for _ in range(y)] for _ in range(x)]

        row_2, col_2 = current_state_2
        map2[row_2][col_2] = 1

        return map2


class MultiAgentDeepQNetworkExternal(SimulatorExternal):
    def __init__(self, network: MultiAgentDeepQNetwork):
        self.name = "MultiAgentDeepQNetwork"
        self.operations = ("choose_action", "store_transition", "learn", "get_fullmap", "init_agent1", "init_agent2")
        self.network = network
    
    def exec(self, operation_name: str, args: list):
        if operation_name == "choose_action":
            assert len(args) == 3
            agent_id, partial_observation, observation = args
            return self.network.choose_action(agent_id, partial_observation, observation)
        elif operation_name == "store_transition":
            assert len(args) == 5
            agent_id, s, a, r, s_ = args
            self.network.store_transition(agent_id, s, a, r, s_)
            return
        elif operation_name == "learn":
            assert len(args) == 1
            agent_id = args[0]
            self.network.learn(agent_id)
            return
        elif operation_name == "get_fullmap":
            assert len(args) == 1
            map_code = args[0]
            return self.network.get_fullmap(map_code)
        elif operation_name == "init_agent1":
            assert len(args) == 3
            x, y, current_state_1= args
            return self.network.init_agent1(x, y, current_state_1)
        elif operation_name == "init_agent2":
            assert len(args) == 3
            x, y, current_state_2= args
            return self.network.init_agent2(x, y, current_state_2)
        else:
            raise NotImplementedError(f"MultiAgentDeepQNetwork: unsupported operation {operation_name}")