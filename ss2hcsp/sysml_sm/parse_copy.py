"""Simulink diagrams."""

from fractions import Fraction
from typing import Dict, List
import lark
from decimal import Decimal
from xml.dom.minidom import NodeList

from ss2hcsp.sl.sl_line import SL_Line, unknownLine
from ss2hcsp.sl.sl_block import get_gcd, SL_Block
from ss2hcsp.matlab import convert
from ss2hcsp.matlab import function
from ss2hcsp.matlab.parser import expr_parser, function_parser, \
    transition_parser, func_sig_parser, state_op_parser
from ss2hcsp.sl.Continuous.clock import Clock
from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.Continuous.signalBuilder import SignalBuilder
from ss2hcsp.sl.Continuous.source import Sine
from ss2hcsp.sl.Continuous.fcn import Fcn
from ss2hcsp.sl.Continuous.transferfcn import TransferFcn
from ss2hcsp.sl.MathOperations.product import Product
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.MathOperations.my_abs import Abs
from ss2hcsp.sl.MathOperations.sqrt import Sqrt
from ss2hcsp.sl.MathOperations.square import Square
from ss2hcsp.sl.LogicOperations.logic import And, Or, Not
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.LogicOperations.reference import Reference
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SignalRouting.scope import Scope
from ss2hcsp.sl.SubSystems.subsystem import Subsystem, Triggered_Subsystem, Enabled_Subsystem
from ss2hcsp.sl.Discontinuities.saturation import Saturation
from ss2hcsp.sl.Discontinuities.hitcross import Hitcross
from ss2hcsp.sl.Discrete.unit_delay import UnitDelay 
from ss2hcsp.sl.Discrete.DiscretePulseGenerator import DiscretePulseGenerator
from ss2hcsp.sl.Discrete.discrete_PID_controller import DiscretePID
from ss2hcsp.sl.MathOperations.min_max import MinMax
from ss2hcsp.sysml_sm.sm_state import AND_State, OR_State, Junction, GraphicalFunction
from ss2hcsp.sysml_sm.sm_chart import SM_Chart
from ss2hcsp.sf.sf_chart import SF_Chart
from ss2hcsp.sysml_sm.sm_transition import Transition
from ss2hcsp.sysml_sm.sm2sf import convert_sm_to_sf
from ss2hcsp.sf.sf_message import SF_Message,SF_Data
from ss2hcsp.sf.sf_event import SF_Event
from ss2hcsp.sl.mux.mux import Mux
from ss2hcsp.sl.mux.selector import Selector
from ss2hcsp.sl.connector import From, Goto
from ss2hcsp.sl.DataStore.DataStore import DataStoreMemory, DataStoreRead
from xml.dom import minidom
from xml.dom import minicompat
import operator


def parse_sample_time(sample_time):
    """Convert sample time in string to integer or decimal."""
    if sample_time is None or sample_time == 'inf':
        return -1
    elif '.' in sample_time:
        v = Decimal(sample_time)
        return int(v * 1000) / Decimal(1000)
    else:
        return int(sample_time)

def parse_value(value, default=None):
    """Parse value to integer or float."""
    if value:
        if '.' in value:
            return Decimal(value)
        elif '[' in value and ']' in value:
            assert len(value) >3
            value = value[1:-1]
            assert len (value.split(":")) == 2
            start_val = value.split(":")[0]
            end_val = value.split(":")[1]
            return range(int(start_val),int(end_val))
        else:
            return int(value)
    else:
        return default

def replace_spaces(name):
    """Replace spaces and newlines in name with underscores."""
    return name.strip().replace(' ', '_').replace('\n', '_').replace('(', '_').replace(')', '_').replace('/', '_')

def get_attribute_value(block, attribute, name=None):
    for node in block.getElementsByTagName("P"):
        if node.getAttribute("Name") == attribute:
            if node.childNodes:
                if not name or name == node.childNodes[0].data:
                    return node.childNodes[0].data
    return None

def get_field_attribute_value(block, attribute):
    for node in block.getElementsByTagName("Field"):
        if node.getAttribute("Name") == attribute:
            return node.childNodes[0].data
    return None

class SL_Diagram:
    """Represents a Simulink diagram."""
    def __init__(self, location=""):
        # Dictionary of blocks indexed by name
        self.blocks_dict: Dict[str, SL_Block] = dict()

        # Dictionary of Stateflow parameters indexed by name
        self.chart_parameters = dict()

        # Dictionary of constants
        self.constants: Dict[str, (int, Decimal, Fraction)] = dict()

        # XML data structure
        self.model = None

        # Name of the diagram, set by parse_xml
        self.name = None

        # Different parts of the diagram
        self.continuous_blocks: List[SL_Block] = list()
        self.discrete_blocks: List[SL_Block] = list()
        self.scopes = list()
        self.dsms = list()
        
        # Parsed model of the XML file
        if location:
            with open(location,encoding="utf-8") as f:
                self.model = minidom.parse(f)

    def parse_stateflow_xml(self):
        """Parse stateflow charts from XML."""

        def get_acts(acts):
            """Convert action into a sequence of actions."""
            lists = list()
            if isinstance(acts, function.Sequence):
                for act in [acts.cmd1, acts.cmd2]:
                    if isinstance(act, function.Sequence):
                        lists.extend(get_acts(act))
                    else:
                        lists.append(act)
            else:
                lists.append(acts)
            return lists

        def get_transitions(blocks):
            """Obtain the list of transitions.
            
            Returns a dictionary mapping transitions IDs to transition objects.
            
            """
            assert isinstance(blocks, minicompat.NodeList)

            tran_dict = dict()
            for transition in blocks:
                assert isinstance(transition, minidom.Node)
                if isinstance(transition, minidom.Element):
                        tran_ssid = transition.getAttribute("xmi:idref")
                        extended_properties = transition.getElementsByTagName("extendedProperties")
                        if extended_properties:
                            # 假设每个 <connector> 节点最多只有一个 <extendedProperties>
                            ext_prop = extended_properties[0]
                
                            # 提取 privatedata2 和 privatedata3
                            guard_expr = ext_prop.getAttribute("privatedata2")
                            effect_body = ext_prop.getAttribute("privatedata3")
                
                            # 打印 privatedata2 和 privatedata3 的内容
                            #print(f"  guard: {guard_expr}")
                            #print(f"  effect: {effect_body}")

                            if guard_expr and effect_body:
                                tran_label = f"{guard_expr}{effect_body}"  # 拼接 guard 和 effect
                            elif guard_expr:
                                tran_label = guard_expr  # 如果只有 guard_expr
                            elif effect_body:
                                tran_label = effect_body  # 如果只有 effect_body
                            else:
                                tran_label = None  # 如果都没有 guard 和 effect
                            #print(f"Transition Label: {tran_label}")

                        if tran_label is None:
                            tran_label = function.TransitionLabel(None, None, None, None)
                        else:
                            try:
                                tran_label = transition_parser.parse(tran_label)
                            except lark.exceptions.UnexpectedToken as e:
                                print("When parsing transition label", tran_label)
                                raise e

                        tran_tags = None
                        for child in transition.childNodes:
                            if child.nodeType == child.ELEMENT_NODE and child.tagName == "tags":
                                tran_tags = child
                                break  # Stop after finding the first <tags> node
                        order = None
                        for child in tran_tags.childNodes:
                            if child.nodeType == child.ELEMENT_NODE and child.tagName == "tag":
                                if child.getAttribute("name") == "Execution order":
                                    order = int(child.getAttribute("value"))
                                    break
                        print(order)       

                        assert len([child for child in transition.childNodes if child.nodeName == "source"]) == 1
                        assert len([child for child in transition.childNodes if child.nodeName == "target"]) == 1
                        src_ssid, dst_ssid = None, None
                        source_node = transition.getElementsByTagName("source")[0]
                        target_node = transition.getElementsByTagName("target")[0]
                        source_model = source_node.getElementsByTagName("model")[0]
                        target_model = target_node.getElementsByTagName("model")[0]

                        # 检查 source_model 和 target_model 的 name 是否为 "Initial"
                        if source_model.getAttribute("name") != "Initial":
                            src_ssid = source_node.getAttribute("xmi:idref")

                        if target_model.getAttribute("name") != "Initial":
                            dst_ssid = target_node.getAttribute("xmi:idref")

                        # There should be no repeated transition IDs
                        assert tran_ssid not in tran_dict
                        tran_dict[tran_ssid] = Transition(ssid=tran_ssid, label=tran_label, order=order,
                                                        src=src_ssid, dst=dst_ssid)
                        print(f"block SSID:{tran_ssid},block labelString:{tran_label},order:{order},block src:{src_ssid},block dst:{dst_ssid}")
            return tran_dict

        all_out_trans = dict()

        def find_node_by_ssid(ssid, root_element):
            """
            查找具有指定 xmi:idref 的节点
            :param ssid: 要查找的 ssid（xmi:idref）
            :param root_element: XML 文档的根元素
            :return: 对应的节点，如果没有找到则返回 None
            """
            # 遍历所有的 <element> 节点
            print(f"root_element:{root_element}")
            # for element in root_element.getElementsByTagName("element"):
            #     if element.getAttribute("xmi:idref") == ssid:
            #         return element  # 找到匹配的节点，返回该节点
            # return None  # 如果没有找到匹配的节点，返回 None
            # 如果传入的是 NodeList 类型（例如 elements），直接遍历
            if isinstance(root_element, NodeList):
                for element in root_element:
                    if element.getAttribute("xmi:idref") == ssid:
                        return element
                return None
            else:
                # 否则当成 DOM 根节点来处理，调用 getElementsByTagName
                for element in root_element.getElementsByTagName("element"):
                    if element.getAttribute("xmi:idref") == ssid:
                        return element
                return None

        def get_all_children(ssid, element_tree):
            """递归获取所有子节点"""
            children = element_tree.get(ssid, [])
            result = set(children)
            for child in children:
                result.update(get_all_children(child, element_tree))
            return result

        def get_parent_map(element_tree):
            """生成子节点到父节点的映射"""
            parent_map = {}
            for parent, children in element_tree.items():
                for child in children:
                    parent_map[child] = parent
            return parent_map
        
        def recursively_children(children, element_tree=None):

            #print(f"Found {len(children)} elements")
            connectors = self.model.getElementsByTagName("connectors")

            # 如果没有找到子元素，返回空列表
            if not children:
                return list(), list(), list()

            _states, _junctions, _functions = list(), list(), list()
            chart_data = dict()
            out_trans_dict = get_transitions(connectors[0].childNodes)
            child_states, child_junctions, child_functions = list(), list(), list()
            for child in children:
                ssid = child.getAttribute("xmi:idref")
                print(f"【recursively_children】 child id:{ssid}")
                state_type = child.getAttribute("xmi:type")
                state_name = child.getAttribute("name")
                if state_type == "uml:Artifact":
                    fun_id = child.getAttribute('xmi:idref')
                    fun_name=child.getAttribute('name')
                    code_elements = child.getElementsByTagName('code')
                    for code_elem in code_elements:
                        fun_script = code_elem.getAttribute('header1')
                        if fun_script:
                            # Has script, directly use parser for matlab functions
                            fun_name = function_parser.parse(fun_script).name
                            _functions.append(function_parser.parse(fun_script))
                            print(f"function labelString:{fun_name},function script:{fun_script}")

                        else:
                            # Otherwise, this is a graphical function
                            children = [c for c in child.childNodes if c.nodeName == "Children"]
                            assert len(children) == 1
                            sub_trans = get_transitions(children[0].childNodes)
                            sub_states, sub_junctions, sub_functions = get_children(child)
                            assert len(sub_states) == 0 and len(sub_functions) == 0

                            try:
                                fun_name, fun_params, fun_return = func_sig_parser.parse(fun_name)
                            except lark.exceptions.UnexpectedToken as e:
                                print("When parsing function signature", fun_name)
                                raise e

                            chart_state1 = OR_State(ssid=ssid, name=fun_name)
                            for state in  sub_junctions:
                                state.father = chart_state1
                                chart_state1.children.append(state)
                            graph_fun = GraphicalFunction(fun_name, fun_params, fun_return, sub_trans, sub_junctions)
                            _functions.append(graph_fun)
                            print(f"functions:{_functions}")
                
                elif state_type == "uml:StateMachine" and ssid in element_tree:
                    # Get the corresponding child nodes from the element_tree
                    referenced_ssids = element_tree[ssid]
                    print(f"Found referenced ssid: {ssid} with children ssids: {referenced_ssids}")
                    referenced_nodes = list()
                    for ref_ssid in referenced_ssids:
                        # Here you would search for these referenced SSIDs in the XML structure
                        referenced_node = find_node_by_ssid(ref_ssid, elements)
                        referenced_nodes.append(referenced_node)
                    print(f"referenced_nodes:{referenced_nodes}")

                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{name}\nex:{exit_body}"
                    
                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    dictMerged2.update(all_out_trans)
                    
                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        #获取order
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break
                        #print(order)  

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    child_states, child_junctions, child_functions = recursively_children(referenced_nodes, element_tree=element_tree)
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state, OR_State):
                                _state.has_history_junc = True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)

                elif state_type == "uml:StateMachine" and ssid not in element_tree:

                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"
                    
                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    dictMerged2.update(all_out_trans)
                    
                    # for tran in dictMerged2.values():
                    #     src, dst = tran.src, tran.dst
                    #     if src is None and dst == ssid:  # it is a default transition
                    #         default_tran = tran
                    #     elif src == ssid:  # the src of tran is this state
                    #         out_trans.append(tran)
                    #     else:
                    #         all_out_trans[tran.ssid] = tran
                    # out_trans.sort(key=operator.attrgetter("order"))
                    # print(f"out_trans:{out_trans}")

                    # # Get inner_trans
                    # inner_trans = list()
                    # grandchildren = [grandchild for grandchild in child.childNodes if grandchild.nodeName == "Children"]
                    # assert len(grandchildren) <= 1
                    # if len(grandchildren) == 1:
                    #     inner_trans_dict = get_transitions(grandchildren[0].childNodes)
                    #     for tran in inner_trans_dict.values():
                    #         src, dst = tran.src, tran.dst
                    #         if src == ssid:
                    #             inner_trans.append(tran)
                    # inner_trans.sort(key=operator.attrgetter("order"))
                    # print(f"inner_trans:{inner_trans}")

                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        #获取order
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break
                        #print(order)  

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    child_states, child_junctions, child_functions = list(), list(), list()
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state, OR_State):
                                _state.has_history_junc = True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)

                elif state_type == "uml:State" and ssid in element_tree:
                    print(f"ssid:{ssid}")
                    # Get the corresponding child nodes from the element_tree
                    referenced_ssids = element_tree[ssid]
                    print(f"Found referenced ssid: {ssid} with children ssids: {referenced_ssids}")
                    referenced_nodes = list()
                    for ref_ssid in referenced_ssids:
                        # Here you would search for these referenced SSIDs in the XML structure
                        print(f"【【【【【ref_ssid:{ref_ssid}】】】】】")
                        referenced_node = find_node_by_ssid(ref_ssid, elements)
                        referenced_nodes.append(referenced_node)
                    print(f"RRRRRreferenced_nodes:{referenced_nodes}")

                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"

                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    #print(f"——dictMerged2:{dictMerged2}")
                    dictMerged2.update(all_out_trans)
                    
                    # for tran in dictMerged2.values():
                    #     src, dst = tran.src, tran.dst
                    #     if src is None and dst == ssid:  # it is a default transition
                    #         default_tran = tran
                    #     elif src == ssid:  # the src of tran is this state
                    #         out_trans.append(tran)
                    #     else:
                    #         all_out_trans[tran.ssid] = tran
                    # out_trans.sort(key=operator.attrgetter("order"))
                    # print(f"out_trans:{out_trans}")

                    # # Get inner_trans
                    # inner_trans = list()
                    # grandchildren = [grandchild for grandchild in child.childNodes if grandchild.nodeName == "Children"]
                    # assert len(grandchildren) <= 1
                    # if len(grandchildren) == 1:
                    #     inner_trans_dict = get_transitions(grandchildren[0].childNodes)
                    #     for tran in inner_trans_dict.values():
                    #         src, dst = tran.src, tran.dst
                    #         if src == ssid:
                    #             inner_trans.append(tran)
                    # inner_trans.sort(key=operator.attrgetter("order"))
                    # print(f"inner_trans:{inner_trans}")

                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    child_states, child_junctions, child_functions = recursively_children(referenced_nodes,element_tree=element_tree)
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state, OR_State):
                                _state.has_history_junc = True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)
                    print(f"!!!_states:{_states}")


                elif state_type == "uml:State":
                    # Extract AND- and OR-states
                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"
                    
                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    #print(f"——dictMerged2:{dictMerged2}")
                    dictMerged2.update(all_out_trans)
                    
                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break
                        #print(order)  

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)
                    _states.append(_state)

                    # Get children states and junctions recursively
                    # child_states, child_junctions, child_functions = get_children(child)
                    # _state.funs = child_functions
                    # for _child in child_states + child_junctions:
                    #     _child.father = _state
                    #     _state.children.append(_child)
                    #     if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                    #         if isinstance(_state, OR_State):
                    #             _state.has_history_junc = True

                #     if _state.children and isinstance(_state.children[0], AND_State):
                #         _state.children.sort(key=operator.attrgetter("order"))
                #     _states.append(_state)
                #     print(f"!!!_states:{_states}")
                    
                # elif state_type == "uml:StateNode":
                #     name = child.getAttribute('name')
                #     if name == "Junction":
                #         ssid = child.getAttribute("xmi:idref")
                #         junc_type = get_attribute_value(block=child, attribute="type") #???没找到该属性的对应属性
                #         # Get default_tran and out_trans
                #         default_tran = None
                #         out_trans = list()

                #         dictMerged2 = dict(out_trans_dict)
                #         dictMerged2.update(all_out_trans)

                #         for tran in dictMerged2.values():
                #             src, dst = tran.src, tran.dst
                #             if src is None and dst == ssid:  # it is a default transition
                #                 default_tran = tran
                #             elif src == ssid:  # the src of tran is this state
                #                 out_trans.append(tran)
                #             else:
                #                 all_out_trans[tran.ssid] = tran
                #         out_trans.sort(key=operator.attrgetter("order"))
                #         # Create a junction object and put it into _junstions
                #         _junctions.append(Junction(ssid=ssid, out_trans=out_trans,junc_type=junc_type, default_tran=default_tran))                       
            
            return _states, _junctions, _functions

        def get_children(block, element_tree=None):
            """获取当前块的子状态、连接点和函数列表"""
            assert isinstance(block, minidom.Element)

            elements = block.getElementsByTagName("elements")[0]
            connectors = block.getElementsByTagName("connectors")
            # 获取所有节点，包括状态和连接点
            children = [child for child in elements.childNodes if child.nodeName == "element"]
            print(f"Found {len(children)} elements")

            # 如果没有找到子元素，返回空列表
            if not children:
                return list(), list(), list()

            _states, _junctions, _functions = list(), list(), list()
            chart_data = dict()
            event_dict = dict()
            out_trans_dict = get_transitions(connectors[0].childNodes)
            child_states, child_junctions, child_functions = list(), list(), list()
            for child in children:
                #print(f"Processing ownedMember: {child.getAttribute('xmi:id')}")
                ssid = child.getAttribute("xmi:idref")
                state_type = child.getAttribute("xmi:type")
                state_name = child.getAttribute("name")
                                
                if state_type == "uml:Artifact":
                    fun_id = child.getAttribute('xmi:idref')
                    fun_name=child.getAttribute('name')
                    code_elements = child.getElementsByTagName('code')
                    for code_elem in code_elements:
                        fun_script = code_elem.getAttribute('header1')
                        if fun_script:
                            # Has script, directly use parser for matlab functions
                            fun_name = function_parser.parse(fun_script).name
                            _functions.append(function_parser.parse(fun_script))
                            print(f"function labelString:{fun_name},function script:{fun_script}")
                        else:
                            # Otherwise, this is a graphical function
                            children = [c for c in child.childNodes if c.nodeName == "Children"]
                            assert len(children) == 1
                            sub_trans = get_transitions(children[0].childNodes)
                            sub_states, sub_junctions, sub_functions = get_children(child)
                            assert len(sub_states) == 0 and len(sub_functions) == 0

                            try:
                                fun_name, fun_params, fun_return = func_sig_parser.parse(fun_name)
                            except lark.exceptions.UnexpectedToken as e:
                                print("When parsing function signature", fun_name)
                                raise e

                            chart_state1 = OR_State(ssid=ssid, name=fun_name)
                            for state in  sub_junctions:
                                state.father = chart_state1
                                chart_state1.children.append(state)
                            graph_fun = GraphicalFunction(fun_name, fun_params, fun_return, sub_trans, sub_junctions)
                            _functions.append(graph_fun)
                            print(f"functions:{_functions}")


                elif state_type == "uml:StateMachine" and ssid in element_tree:
                    # Get the corresponding child nodes from the element_tree
                    referenced_ssids = element_tree[ssid]
                    print(f"Found referenced ssid: {ssid} with children ssids: {referenced_ssids}")
                    referenced_nodes = list()
                    for ref_ssid in referenced_ssids:
                        # Here you would search for these referenced SSIDs in the XML structure
                        referenced_node = find_node_by_ssid(ref_ssid, elements)
                        referenced_nodes.append(referenced_node)
                    print(f"RRRRRreferenced_nodes:{referenced_nodes}")

                    labels = state_name
                    states = child.getElementsByTagName("states")
                    #states = [node for node in child.childNodes if node.nodeType == node.ELEMENT_NODE and node.tagName == 'states']
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                            #entry = f"en:{entry_body}"
                            #labels += f"\n{entry}"
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                            #do = f"du:{do_body}"
                            #labels += f"\n{do}"
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                            #exit = f"ex:{exit_body}"
                            #labels += f"\n{exit}"
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"
                    
                    #labels = get_attribute_value(child, "labelString")
                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    dictMerged2.update(all_out_trans)
                    
                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        #获取order
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break
                        #print(order)  

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    child_states, child_junctions, child_functions = recursively_children(referenced_nodes, element_tree=element_tree)
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state, OR_State):
                                _state.has_history_junc = True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)
                    

                elif state_type == "uml:StateMachine" and ssid not in element_tree:
                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"
                    
                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    dictMerged2.update(all_out_trans)
                    
                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break
                        #print(order)  

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    # child_states, child_junctions, child_functions = get_children(child)
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state, OR_State):
                                _state.has_history_junc = True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)
                    print(f"!!!{_states}")


                elif state_type == "uml:State" and ssid in element_tree:
                    # Get the corresponding child nodes from the element_tree
                    referenced_ssids = element_tree[ssid]
                    print(f"Found referenced ssid: {ssid} with children ssids: {referenced_ssids}")
                    referenced_nodes = list()
                    for ref_ssid in referenced_ssids:
                        # Here you would search for these referenced SSIDs in the XML structure
                        referenced_node = find_node_by_ssid(ref_ssid, elements)
                        referenced_nodes.append(referenced_node)
                    print(f"RRRRRreferenced_nodes:{referenced_nodes}")

                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"

                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    #print(f"——dictMerged2:{dictMerged2}")
                    dictMerged2.update(all_out_trans)
                    
                    # for tran in dictMerged2.values():
                    #     src, dst = tran.src, tran.dst
                    #     if src is None and dst == ssid:  # it is a default transition
                    #         default_tran = tran
                    #     elif src == ssid:  # the src of tran is this state
                    #         out_trans.append(tran)
                    #     else:
                    #         all_out_trans[tran.ssid] = tran
                    # out_trans.sort(key=operator.attrgetter("order"))
                    # print(f"out_trans:{out_trans}")

                    # # Get inner_trans
                    # inner_trans = list()
                    # grandchildren = [grandchild for grandchild in child.childNodes if grandchild.nodeName == "Children"]
                    # assert len(grandchildren) <= 1
                    # if len(grandchildren) == 1:
                    #     inner_trans_dict = get_transitions(grandchildren[0].childNodes)
                    #     for tran in inner_trans_dict.values():
                    #         src, dst = tran.src, tran.dst
                    #         if src == ssid:
                    #             inner_trans.append(tran)
                    # inner_trans.sort(key=operator.attrgetter("order"))
                    # print(f"inner_trans:{inner_trans}")
                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    child_states, child_junctions, child_functions = recursively_children(referenced_nodes, element_tree=element_tree)
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state, OR_State):
                                _state.has_history_junc = True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)
                    print(f"!!!_states:{_states}")

                elif state_type == "uml:State" and ssid not in element_tree and all(ssid not in v for v in element_tree.values()):

                    labels = state_name
                    states = child.getElementsByTagName("states")
                    entry_body, do_body, exit_body = None, None, None
                    for state in states:
                        s_type = state.getAttribute("type")
                        print(f"state type:{s_type}")
                        if s_type == "entry":
                            entry_body = state.getAttribute("name")
                        if s_type == "Transition":
                            do_body = state.getAttribute("name")
                        if s_type == "exit":
                            exit_body = state.getAttribute("name")
                    if entry_body and do_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body and do_body:
                        labels = f"{state_name}\nen:{entry_body}\ndu:{do_body}"
                    elif entry_body and exit_body:
                        labels = f"{state_name}\nen:{entry_body}\nex:{exit_body}"
                    elif do_body and exit_body:
                        labels = f"{state_name}\ndu:{do_body}\nex:{exit_body}"
                    elif entry_body:
                        labels = f"{state_name}\nen:{entry_body}"
                    elif do_body:
                        labels = f"{state_name}\ndu:{do_body}"
                    elif exit_body:
                        labels = f"{state_name}\nex:{exit_body}"

                    print(f"state labelString:{labels}")
                    label = state_op_parser.parse(labels)
                    name = str(label.name)
                    print(f"label name:{name}")
                        
                    # Get en, du and ex actions
                    en = get_acts(label.en_op.op) if label.en_op is not None else []
                    du = get_acts(label.du_op.op) if label.du_op is not None else []
                    ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                    print(f"en:{en},du:{du},ex:{ex}")
                        
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict(out_trans_dict)
                    #print(f"——dictMerged2:{dictMerged2}")
                    dictMerged2.update(all_out_trans)
                    
                    inner_trans = list()
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        print(f"src:{src},dst:{dst}")
                        
                        if src is None and dst == ssid:
                            # 默认转换：目标是当前状态
                            default_tran = tran

                        elif ssid in element_tree:
                            # 当前状态是父节点，判断是否是内部转换（父 -> 子 或 子 -> 父）
                            if (src == ssid and dst in element_tree[ssid]) or (dst == ssid and src in element_tree[ssid]):
                                inner_trans.append(tran)
                            elif src == ssid:
                                # 是出边，但不是内部转换
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                        else:
                            # 当前状态不在element_tree中，无法判断是否内部，只能按默认逻辑处理
                            if src == ssid:
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran

                    out_trans.sort(key=operator.attrgetter("order"))
                    print(f"out_trans:{out_trans}")

                    inner_trans.sort(key=operator.attrgetter("order"))
                    print(f"inner_trans:{inner_trans}")

                    # Create a state object
                    if state_type == "uml:StateMachine":
                        assert default_tran is None and out_trans == [], \
                            "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                        tran_tags = None
                        for tags in child.childNodes:
                            if tags.nodeType == tags.ELEMENT_NODE and tags.tagName == "tags":
                                tran_tags = tags
                                break  # Stop after finding the first <tags> node
                        order = None
                        for tag in tags.childNodes:
                            if tag.nodeType == tag.ELEMENT_NODE and tag.tagName == "tag":
                                if tag.getAttribute("name") == "Execution order":
                                    order = int(tag.getAttribute("value"))
                                    break

                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                            order=order)
                    elif state_type == "uml:State":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                        en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)

                    # Get children states and junctions recursively
                    # child_states, child_junctions, child_functions = recursively_children(child)
                    # _state.funs = child_functions
                    # for _child in child_states + child_junctions:
                    #     _child.father = _state
                    #     _state.children.append(_child)
                    #     if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                    #         if isinstance(_state, OR_State):
                    #             _state.has_history_junc = True

                    # if _state.children and isinstance(_state.children[0], AND_State):
                    #     _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)
                    print(f"!!!_states:{_states}")
                    
                elif state_type == "uml:StateNode":
                    name = child.getAttribute('name')
                    if name == "Junction":
                        ssid = child.getAttribute("xmi:idref")
                        junc_type = get_attribute_value(block=child, attribute="type") #???没找到该属性的对应属性
                        # Get default_tran and out_trans
                        default_tran = None
                        out_trans = list()

                        dictMerged2 = dict(out_trans_dict)
                        dictMerged2.update(all_out_trans)

                        for tran in dictMerged2.values():
                            src, dst = tran.src, tran.dst
                            if src is None and dst == ssid:  # it is a default transition
                                default_tran = tran
                            elif src == ssid:  # the src of tran is this state
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran
                        out_trans.sort(key=operator.attrgetter("order"))
                        # Create a junction object and put it into _junstions
                        _junctions.append(Junction(ssid=ssid, out_trans=out_trans,junc_type=junc_type, default_tran=default_tran))

                elif state_type == "uml:DataType":
                    for data in child.getElementsByTagName(name="attribute"):
                        var_name = data.getAttribute("name")
                        print(f"var name:{var_name}")
                        value_node = data.getElementsByTagName("initial")
                        value = value_node[0].getAttribute("body")
                        if value:
                            value = int(value)
                        else:
                            value = None
                            print(f"{var_name} value:{value}")
                        if value is not None:
                            try:
                                value = expr_parser.parse(value)
                            except lark.exceptions.UnexpectedToken as e:
                                print("When parsing value:", value)
                                raise e
                        else:
                            value = 0
                        scope = data.getAttribute("scope")
                        sf_data = SF_Data(name=var_name, value=value, scope=scope)
                        if data.getElementsByTagName(name="message"):
                            mesgNode = data.getElementsByTagName(name="message")[0]
                            if get_attribute_value(mesgNode, "isMessage") == "1":
                                message = SF_Message(name=var_name, data=0, scope=scope)
                                message_dict[var_name] = message
                        else:
                            chart_data[var_name] = sf_data                          

                elif state_type == "uml:Event":
                    event_name = child.getAttribute("name")
                    for i, e in enumerate(child.getElementsByTagName(name="properties")):
                        print(f"i:{i}\ne:{e}")
                        event_scope = e.getAttribute("scope")
                        port = i + 1
                        if get_attribute_value(e, "trigger"):
                            event_trigger = get_attribute_value(e, "trigger")
                        else:
                            event_trigger = None
                        event = SF_Event(name=event_name, scope=event_scope, trigger=event_trigger, port=port)
                        event_dict[event_name] = event

            
            return _states, _junctions, _functions, chart_data, event_dict
        
        charts = self.model.getElementsByTagName("xmi:Extension")
        # 获取elements节点
        elements_node = self.model.getElementsByTagName("elements")[0]
        print(elements_node)

        # 获取所有的element节点
        elements = elements_node.getElementsByTagName("element")
        print(f"Found {len(elements)} elements.")

        # 用于存储element的父子关系
        element_tree = {}

        # 先通过xmi:idref创建一个元素ID的映射字典
        id_to_element = {}
        for element in elements:
            element_id = element.getAttribute("xmi:idref")
            id_to_element[element_id] = element

        # 遍历所有element节点，构建父子关系
        for element in elements:
            # 获取每个element的model节点（如果存在的话）
            model_nodes = element.getElementsByTagName("model")
    
            if model_nodes:
                model = model_nodes[0]
        
                # 如果model节点有owner属性
                if model.hasAttribute("owner"):
                    owner_id = model.getAttribute("owner")  # 获取owner指向的ID
            
                    # 通过owner_id查找对应的父节点
                    parent_element = id_to_element.get(owner_id)
            
                    # 将父子关系保存到字典中
                    if parent_element is not None:
                        parent_node_id = parent_element.getAttribute("xmi:idref")
                        if parent_node_id not in element_tree:
                            element_tree[parent_node_id] = []
                        element_tree[parent_node_id].append(element.getAttribute("xmi:idref"))

        # 输出所有父子关系
        for parent_node_id, children in element_tree.items():
            print(f"父节点ID: {parent_node_id}  子节点ID: {', '.join(children)}")
        print(f"element tree:{element_tree}")

        for chart in charts:
            all_out_trans = dict()
            chart_id = chart.getAttribute("extenderID")
            print(f"chart_id:{chart_id}")
            #chart_name = chart.getAttribute("extender")
            chart_name = "Chart"
            print(f"chart_name:{chart_name}")

            # A chart is wrapped into an AND-state
            chart_state = AND_State(ssid=chart_id, name=chart_name)
            states, junctions, functions, chart_data, event_dict = get_children(block=chart, element_tree=element_tree)

            chart_state.funs = functions
            for state in states + junctions:
                state.father = chart_state
                chart_state.children.append(state)
 
            if chart_state.children and isinstance(chart_state.children[0], AND_State):
                chart_state.children.sort(key=operator.attrgetter("order"))
            assert chart_state.check_children()
        
            chart_st = get_attribute_value(block=chart, attribute="sampleTime")
            if chart_st:
                if '.' in chart_st or 'e' in chart_st:
                    chart_st = Decimal(chart_st)
                else:
                    chart_st = int(chart_st)
            else:
                chart_st = -1
            
            message_dict = dict()

            assert chart_name not in self.chart_parameters
            self.chart_parameters[chart_name] = {
                "state": chart_state,
                "data": chart_data,
                "st": chart_st,
                "message_dict": message_dict,
                "event_dict": event_dict
            }
            print(f"Chart Parameters for {chart_name}:")
            print(f"  State: {chart_state.name}, Sample Time: {chart_st}")
            print(f"  Events: {', '.join(event_dict.keys())}")
            print(f"  Data: {', '.join(chart_data.keys())}")
            print(f"  Messages: {', '.join(message_dict.keys())}")

    def parse_xml(self, block_parameters=(),mask_parameters=()):
        # 加一个dict，要维护里面的值
        if not mask_parameters:
            mask_parameters=dict()

        # Extract BlockParameterDefaults
        if not block_parameters:
            block_parameters = dict() #para[def]=dict() para[operator]=
            default_para_blocks = self.model.getElementsByTagName("profileApplication")
            assert len(default_para_blocks) >= 1
            for child in default_para_blocks[0].childNodes:
                if child.nodeName == "appliedProfile":
                    child_type = child.getAttribute("xmi:type")
                    assert child_type not in block_parameters
                    block_parameters[child_type] = dict()
                    block_parameters[child_type]["SampleTime"]= get_attribute_value(child, "SampleTime")
                    block_parameters[child_type]["Operator"] = get_attribute_value(child, "Operator")
                    block_parameters[child_type]["HitCrossingOffset"] = get_attribute_value(child, "HitCrossingOffset")
                    block_parameters[child_type]["HitCrossingDirection"] = get_attribute_value(child, "HitCrossingDirection")
                    block_parameters[child_type]["ZeroCross"] = get_attribute_value(child, "ZeroCross")
                    
        self.parse_stateflow_xml()

        # Extract name of the model
        models = self.model.getElementsByTagName("uml:Model")
        assert len(models) <= 1
        self.name = ""
        if models:
            self.name = models[0].getAttribute("name")
        print(f"model name:{self.name}")

        system = self.model.getElementsByTagName("diagrams")[0]
        print(f"system:{system}")

        workspace = self.model.getElementsByTagName("ModelWorkspace")
        if workspace:
            matstructs = workspace[0].getElementsByTagName("MATStruct")
            for struct in matstructs:
                name = get_field_attribute_value(struct, "Name")
                value = parse_value(get_field_attribute_value(struct, "Value"))
                self.constants[name] = value

        diagram = system.getElementsByTagName("diagram")[0]
        # Add blocks
        blocks = [child for child in diagram.childNodes if child.nodeName == "properties"]

        # The following dictionary is used to replace port names as
        # formatted ones. The name of each port shoud be in the form of
        # port_type + port_number, such as in_0 and out_1 in order to delete
        # subsystems successfully (see function delete_subsystems in get_hcsp.py).
        port_name_dict = dict()  # mapping from old name to new name

        for block in blocks:
            # Type of block
            block_type = block.getAttribute("type")
            print(f"block type:{block_type}")

            # Block name.
            #block_name = replace_spaces(block.getAttribute("name"))
            block_name = "Chart"
            print(f"block name:{block_name}")

            # Sample time of block
            sample_time = get_attribute_value(block, "SampleTime")
            if (not sample_time) and block_type in block_parameters:
                sample_time = block_parameters[block_type]["SampleTime"]
            sample_time = parse_sample_time(sample_time)

            # For each type of block, obtain additional parameters
            if block_type == "Mux":
                inputs = get_attribute_value(block, "Inputs")
                ports = list(arg.value for arg in expr_parser.parse(get_attribute_value(block=block, attribute="Ports")).args)
                self.add_block(Mux(name=block_name, inputs=inputs, ports=ports))
            elif block_type == "Statechart":
                #subsystem = block.getElementsByTagName("System")[0]
                #print(subsystem.getAttribute("name"))

                # Check if it is a Signal Builder
                is_signal_builder = False
                for child in block.childNodes:
                    if child.nodeName == "Object" and child.getAttribute("PropName") == "MaskObject":
                        for child_para in child.childNodes:
                            if child_para.nodeName == "Object" and child_para.getAttribute("PropName") == "Parameters":
                                para_name = get_attribute_value(block=child_para, attribute="Name")
                                para_val = parse_value(get_attribute_value(block=child_para, attribute="Value"),default=0)
                                mask_parameters[para_name]=para_val
                        if get_attribute_value(block=child, attribute="Type") == "Sigbuilder block":
                            is_signal_builder = True
                            break
                if is_signal_builder:
                    signal_names = []
                    time_axises = []
                    data_axises = []
                    out_indexs = []
                    for node in subsystem.getElementsByTagName("Array"):
                        if node.getAttribute("PropName") == "Signals":
                            # assert node.getAttribute("Type") == "SigSuiteSignal"
                            for obj in node.getElementsByTagName("Object"):
                                signal_names.append(block_name + "_" + get_attribute_value(obj, "Name"))
                                xData = get_attribute_value(obj, "XData")
                                out_index = get_attribute_value(obj, "outIndex")
                                out_indexs.append(out_index)
                                # if "\n" in xData:
                                #     xData = xData.split("\n")[1]
                                assert xData.count('[') == xData.count(']') == 1
                                start = xData.index('[')
                                end = xData.index(']')
                                time_axises.append(tuple(parse_sample_time(e) for e in xData[start+1:end].split(',')))
                                yData = get_attribute_value(obj, "YData")
                                # if "\n" in yData:
                                #     yData = yData.split("\n")[1]
                                assert yData.count('[') == yData.count(']') == 1
                                start = yData.index('[')
                                end = yData.index(']')
                                data_axises.append(tuple(parse_value(e) for e in yData[start+1:end].split(',')))

                    if not signal_names:
                        for node in subsystem.getElementsByTagName("Object"):
                            if node.getAttribute("PropName") == "Signals":
                                signal_names.append(block_name + "_" + get_attribute_value(node, "Name"))
                                xData = get_attribute_value(node, "XData")
                                # if "\n" in xData:
                                #     xData = xData.split("\n")[1]
                                # time_axises.append(tuple(float(e) for e in xData[1:-1].split(',')))
                                assert xData.count('[') == xData.count(']') == 1
                                start = xData.index('[')
                                end = xData.index(']')
                                time_axises.append(tuple(parse_sample_time(e) for e in xData[start + 1:end].split(',')))
                                yData = get_attribute_value(node, "YData")
                                # if "\n" in yData:
                                #     yData = yData.split("\n")[1]
                                # data_axises.append(tuple(float(e) for e in yData[1:-1].split(',')))
                                assert yData.count('[') == yData.count(']') == 1
                                start = yData.index('[')
                                end = yData.index(']')
                                data_axises.append(tuple(parse_value(e) for e in yData[start + 1:end].split(',')))

                    assert signal_names
                    self.add_block(SignalBuilder(name=block_name, signal_names=tuple(signal_names),
                                                 time_axises=time_axises, data_axises=data_axises))
                    continue

                # Check if it is a stateflow chart
                sf_block_type = replace_spaces(block.getAttribute("name"))
                if sf_block_type == "Chart":
                    print(f"sf block type:{sf_block_type}")
                    chart_paras = self.chart_parameters[block_name]
                    print(f"chart paras:{chart_paras}")
                    # ports = list(arg.value for arg in expr_parser.parse(get_attribute_value(block=block, attribute="Ports")).args)
                    # print(f"ports:{ports}")
                    # if len(ports) == 0:
                    #     ports = [0, 0]
                    # elif len(ports) == 1:
                    #     ports.append(0)
                    ports = [0, 0]
                    num_dest, num_src = ports[:2]
                    print(f"num dest:{num_dest}, num src:{num_src}")

                    # Check if it a triggered stateflow chart
                    triggers = [child for child in block.childNodes if child.nodeName == "Block" and
                                child.getAttribute("BlockType") == "TriggerPort"]
                    print(f"triggers:{triggers}")
                    assert len(triggers) <= 1
                    st = -2 if triggers else chart_paras['st']

                    sysml = SM_Chart(name=block_name, state=chart_paras["state"], data=chart_paras["data"],
                                         num_src=num_src, num_dest=num_dest, st=st)
                    print(f"sysml:\n{sysml}")
                    stateflow = convert_sm_to_sf(sysml)
                    print(f"stateflow:\n{stateflow}")
                    # stateflow = SF_Chart(name=block_name, state=chart_paras["state"], data=chart_paras["data"],
                    #                      num_src=num_src, num_dest=num_dest, st=st)
                    # print(f"stateflow:\n{stateflow}")


                    if triggers:  # it is a triggered stateflow chart
                        trigger_type = get_attribute_value(triggers[0], "TriggerType")
                        
                        if not trigger_type:
                            trigger_type = "rising"
                        assert trigger_type in ["rising", "falling", "either","function-call"]
                        stateflow.trigger_type = trigger_type
                        stateflow.num_dest += 1
                        stateflow.dest_lines.append(None)
                        # Extract the input events
                        stateflow_blocks = self.model.getElementsByTagName("Stateflow")
                        assert len(stateflow_blocks) == 1
                        charts = stateflow_blocks[0].getElementsByTagName("chart")
                        for chart in charts:
                            if get_attribute_value(block=chart, attribute="name", name=stateflow.name):
                                events = chart.getElementsByTagName("event")
                                for event in events:
                                    event_name = get_attribute_value(block=event, attribute="name")
                                    event_scope = get_attribute_value(block=event, attribute="scope")
                                    if event_scope == "INPUT_EVENT":
                                        event_trigger = get_attribute_value(block=event, attribute="trigger")
                                        if event_trigger == "RISING_EDGE_EVENT":
                                            event_trigger = "rising"
                                        elif event_trigger == "FALLING_EDGE_EVENT":
                                            event_trigger = "falling"
                                        elif event_trigger == "EITHER_EDGE_EVENT":
                                            event_trigger = "either"
                                        elif event_trigger == "FUNCTION_CALL_EVENT":
                                            event_trigger = "function-call"
                                        else:
                                            raise RuntimeError("Not implemented yet")
                                        stateflow.input_events.append((event_trigger, event_name))
                                break

                    assert stateflow.port_to_in_var == dict() and stateflow.port_to_out_var == dict()
                    for child in block.childNodes:
                        if child.nodeName == "Block":
                            if child.getAttribute("BlockType") == "Inport":
                                in_var = child.getAttribute("Name")
                                port_id = get_attribute_value(child, "Port")
                                port_id = int(port_id) - 1 if port_id else 0
                                assert port_id not in stateflow.port_to_in_var
                                stateflow.port_to_in_var[port_id] = in_var
                            elif child.getAttribute("BlockType") == "Outport":
                                out_var = child.getAttribute("Name")
                                if out_var.find("()") == -1:
                                    port_id = get_attribute_value(child, "Port")
                                    port_id = int(port_id) - 1 if port_id else 0
                                    assert port_id not in stateflow.port_to_out_var
                                    stateflow.port_to_out_var[port_id] = out_var

                    self.add_block(stateflow)
                    continue

                # Check if it is a triggered or enabled subsystem
                triggers = [child for child in subsystem.childNodes if child.nodeName == "Block" and
                            child.getAttribute("BlockType") == "TriggerPort"]
                enables = [child for child in subsystem.childNodes if child.nodeName == "Block" and
                           child.getAttribute("BlockType") == "EnablePort"]
                # Enabled and triggered subsystems haven't been considered
                assert len(triggers) + len(enables) <= 1
                if triggers:  # it is a triggered subsystem
                    trigger_type = get_attribute_value(triggers[0], "TriggerType")
                    if not trigger_type:
                        trigger_type = "rising"
                    assert trigger_type in ["rising", "falling", "either", "function-call"]
                    ports = get_attribute_value(block, "Ports")
                    num_dest, num_src, _, _ = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Triggered_Subsystem(block_name, num_src, num_dest+1, trigger_type)
                    # Why num_src+1 above?
                    # A: The number of normal in-ports (num_src) + one TriggerPort
                elif enables:
                    assert get_attribute_value(enables[0], "StatesWhenEnabling") is None
                    assert get_attribute_value(enables[0], "PropagateVarSize") is None
                    ports = get_attribute_value(block, "Ports")
                    num_dest, num_src, _ = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Enabled_Subsystem(block_name, num_src, num_dest+1)
                else:  # it is a normal subsystem
                    ports = get_attribute_value(block=block, attribute="Ports")
                    num_dest, num_src = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Subsystem("subsystem", block_name, num_src, num_dest, st=sample_time)
                subsystem.diagram = SL_Diagram()
                # Parse subsystems recursively
                subsystem.diagram.model = block
                subsystem.diagram.parse_xml(block_parameters,mask_parameters)
                self.add_block(subsystem)
            elif block_type == "CallbackButton": #link，open doc
                continue
            else:
                raise NotImplementedError("Unhandled block type: %s" % block_type)
        mask_parameters=dict() #refresh mask_parameters after all blocks are renewed by para

        # Add lines
        lines = [child for child in system.childNodes if child.nodeName == "Line"]
        for line in lines:
            line_name = get_attribute_value(block=line, attribute="Name")
            if not line_name:
                line_name = "?"
            ch_name = "?"
            src_block = replace_spaces(get_attribute_value(block=line, attribute="SrcBlock"))
            if src_block in port_name_dict:  # an input port
                ch_name = self.name + "_" + src_block
                src_block = port_name_dict[src_block]
            elif src_block not in self.blocks_dict:
                continue
            src_port = int(get_attribute_value(block=line, attribute="SrcPort")) - 1
            branches = [branch for branch in line.getElementsByTagName(name="Branch")
                        if not branch.getElementsByTagName(name="Branch")]
            if not branches:
                branches = [line]
            for branch in branches:
                dest_block = replace_spaces(get_attribute_value(block=branch, attribute="DstBlock"))
                if dest_block in port_name_dict:  # an output port
                    ch_name = self.name + "_" + dest_block
                    dest_block = port_name_dict[dest_block]
                dest_port = get_attribute_value(block=branch, attribute="DstPort")
                dest_port = -1 if dest_port in ["trigger", "enable"] else int(dest_port) - 1
                if dest_block in self.blocks_dict:
                    self.add_line(src=src_block, dest=dest_block, src_port=src_port, dest_port=dest_port,
                                  name=line_name, ch_name=ch_name)

    def add_block(self, block: SL_Block) -> None:
        """Add given block to the diagram."""
        assert block.name not in self.blocks_dict
        self.blocks_dict[block.name] = block

    def add_line(self, src: str, dest: str, src_port: int, dest_port: int, *, name="?", ch_name="?") -> None:
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port, name=name, ch_name=ch_name)
        src_block = self.blocks_dict[line.src]
        dest_block = self.blocks_dict[line.dest]
        line.src_block = src_block
        line.dest_block = dest_block
        src_block.add_src(line.src_port, line)
        dest_block.add_dest(line.dest_port, line)

    def __str__(self):
        result = ""
        result += "\n".join("%s = %s" % (k, v) for k, v in self.constants.items())
        result += "\n".join(str(block) for block in self.blocks_dict.values())
        return result

    def check(self):
        """Checks the diagram is valid. Among the checks are:

        For each block, each dest port is filled, each src port has
        at least one outgoing line.

        """
        pass

    def add_line_name(self):
        """Give each group of lines a name."""
        num_lines = 0
        for block in self.blocks_dict.values():
            # Give name to the group of lines containing each
            # incoming line (if no name is given already).
            for line in block.dest_lines:
                if line:
                    src, src_port = line.src, line.src_port
                    line_group = self.blocks_dict[src].src_lines[src_port]
                    if line_group[0].name == "?":
                        for line2 in line_group:
                            line2.name = "x" + str(num_lines)
                        num_lines += 1

            # Give name to each group of outgoing lines (if no
            # name is given already).
            for lines in block.src_lines:
                if lines and lines[0].name == "?":
                    for line in lines:
                        line.name = "x" + str(num_lines)
                    num_lines += 1

        # Add channel name for each line
        for block in self.blocks_dict.values():
            for line in block.dest_lines:
                if line:
                    assert line.name != "?"
                    if line.ch_name == "?":
                        line.ch_name = "ch_" + line.name + "_" + str(line.branch)
            for lines in block.src_lines:
                for line in lines:
                    assert line.name != "?"
                    if line.ch_name == "?":
                        line.ch_name = "ch_" + line.name + "_" + str(line.branch)

    def comp_inher_st(self):
        """Compute the sample time for each block with inherent sample time."""
        # Propagation
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == -1:

                    # Deal with triggered subsystems
                    if block.type == "triggered_subsystem":
                        trig_line = block.dest_lines[-1]
                        in_block = self.blocks_dict[trig_line.src]
                        if in_block.st >= 0:
                            block.st = in_block.st
                            block.is_continuous = (block.st == 0)
                            terminate = False
                        continue

                    in_st = []  # list of sample times of inputs of the block
                    for line in block.dest_lines:
                        in_block = self.blocks_dict[line.src]
                        # Xiong: Why can't in_block be a stateflow chart?
                        if not isinstance(in_block, SM_Chart) and in_block.st > 0:
                            in_st.append(in_block.st)
                        elif isinstance(in_block, Constant):
                            continue
                        else:
                            in_st = None
                            break
                    if in_st:
                        block.st = get_gcd(sample_times=in_st)
                        block.is_continuous = (block.st == 0)
                        terminate = False

        # Back-propagation
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == -1:
                    out_st = []  # list of sample times of outputs of the block
                    for lines in block.src_lines:
                        for line in lines:
                            out_block = self.blocks_dict[line.dest]
                            if out_block.st > 0:
                                out_st.append(out_block.st)
                            else:
                                out_st = []
                                break
                    if out_st:
                        block.st = get_gcd(sample_times=out_st)
                        block.is_continuous = (block.st == 0)
                        terminate = False
                
        # Re-classify the constant blocks
        for block in self.blocks_dict.values():
            if block.type == "constant":
                dest_block = self.blocks_dict[block.src_lines[0][0].dest]
                block.st = dest_block.st
                block.is_continuous = dest_block.is_continuous

    def inherit_to_continuous(self):
        for block in self.blocks_dict.values():
            if not isinstance(block, SM_Chart) and block.st == -1:
                block.st = 0
                block.is_continuous = True

    def delete_subsystems(self,alias_from_father=""):
        """Unfold subsystems from the current diagram."""
        # Maintain list of subsystems (to be removed) and list of blocks
        # in those subsystems (to be added to self).
        subsystems = []
        blocks_in_subsystems = []

        for block in self.blocks_dict.values():
            block_old_name = block.name
            if alias_from_father !="":
                block.name =  alias_from_father +"_sub_"+ block.name
            if block.type in ["subsystem", "enabled_subsystem"]:
                # Collect all subsystems to be deleted
                subsystems.append(block_old_name)
                # The subsystem is treated as a diagram
                subsystem = block.diagram
                # Delete subsystems recursively
                subsystem.delete_subsystems(block.name)
                # Move all blocks except ports from the subsystem to the parent system
                blocks_dict_rename={}
                for sub_block in subsystem.blocks_dict.values():
                    if sub_block.type =="in_port":
                        # blocks of in_port
                        sub_block_temp = sub_block
                        if sub_block_temp.src_lines:
                            for output_line in sub_block_temp.src_lines[0]:
                                if output_line.dest_block:
                                    output_line.dest= output_line.dest_block.name 
                        blocks_dict_rename[sub_block.name]= sub_block_temp
                    elif sub_block.type =="out_port":
                        # blocks of out_port
                        sub_block_temp = sub_block
                        for port_id in range(sub_block_temp.num_dest):
                            input_line = sub_block_temp.dest_lines[port_id]
                            if input_line.src_block:
                                input_line.src = input_line.src_block.name
                        blocks_dict_rename[sub_block.name]= sub_block_temp
                    else:
                        sub_block_temp = sub_block
                        # sub_block_temp.alias_father = block.name
                        for port_id in range(sub_block_temp.num_dest):
                            input_line = sub_block_temp.dest_lines[port_id]
                            if input_line.dest_block:
                                input_line.dest= input_line.dest_block.name
                            if input_line.src_block:
                                input_line.src = input_line.src_block.name
                        if sub_block_temp.src_lines:
                            for output_line in sub_block_temp.src_lines[0]:
                                if output_line.dest_block:
                                    output_line.dest= output_line.dest_block.name
                                if output_line.src_block:
                                    output_line.src = output_line.src_block.name
                        blocks_dict_rename[sub_block_temp.name]= sub_block_temp
                        
                        blocks_in_subsystems.append(sub_block_temp)
                       
                subsystem.blocks_dict = blocks_dict_rename
                # Sort the input ports in the subsystem by name
                input_ports = [sub_block for sub_block in subsystem.blocks_dict.values()
                               if sub_block.type == "in_port"]
                input_ports.sort(key=operator.attrgetter('name'))
                # Sort the output ports in the subsystem by name
                output_ports = [sub_block for sub_block in subsystem.blocks_dict.values()
                                if sub_block.type == "out_port"]
                output_ports.sort(key=operator.attrgetter('name'))

                # For each input line, find what is the source of this line
                # (in the current diagram or in other subsystems), and make the
                # new connections.
                for port_id in range(block.num_dest):
                    input_line = block.dest_lines[port_id]
                    # # change name in input_line
                    # if hasattr(block,"alias_father"):
                    #     if input_line.src_block.type not in ["in_port", "out_port"]:
                    #         input_line.src = block.alias_father +"_sub_"+ input_line.src
                    #     if input_line.dest_block.type not in ["in_port", "out_port"]:
                    #         input_line.dest = block.alias_father +"_sub_"+ input_line.dest
                    # Find the source
                    src_block = None
                    if input_line.src in self.blocks_dict:
                        src_block = self.blocks_dict[input_line.src]
                    else:
                        for subsys in subsystems:
                            if input_line.src in self.blocks_dict[subsys].diagram.blocks_dict:
                                src_block = self.blocks_dict[subsys].diagram.blocks_dict[input_line.src]
                                break

                    # Delete the old line (input_line) from src_block
                    assert src_block is not None, "delete_subsystems: src_block not found."
                    src_block.src_lines[input_line.src_port][input_line.branch] = unknownLine

                    # Get the corresponding input port in the subsystem
                    port = input_ports[port_id]
                    # assert port.name == "in_" + str(port_id)
                    for port_line in port.src_lines[0]:
                        dest_block = subsystem.blocks_dict[port_line.dest]
                        # Generate a new input line
                        new_input_line = SL_Line(src=src_block.name, dest=dest_block.name,
                                                 src_port=input_line.src_port, dest_port=port_line.dest_port)
                        new_input_line.name = input_line.name
                        # Delete the old line (port_line) and add a new one
                        dest_block.add_dest(port_line.dest_port, new_input_line)
                        # Add a new line for src_block
                        src_block.add_src(input_line.src_port, new_input_line)

                # For each output line, find what is the destination
                # (in the current diagram or in other diagrams), and make
                # the new connections.
                for port_id in range(block.num_src):
                    port = output_ports[port_id]

                    # assert port.name == "out_" + str(port_id)
                    port_line = port.dest_lines[0]
                    src_block = subsystem.blocks_dict[port_line.src]

                    # Delete the old line (port_line) from src_block
                    src_block.src_lines[port_line.src_port][port_line.branch] = unknownLine
                    for output_line in block.src_lines[port_id]:
                        dest_block = None
                        if output_line.dest in self.blocks_dict:
                            dest_block = self.blocks_dict[output_line.dest]
                        else:
                            for subsys in subsystems:
                                if output_line.dest in self.blocks_dict[subsys].diagram.blocks_dict:
                                    dest_block = self.blocks_dict[subsys].diagram.blocks_dict[output_line.dest]
                                    break

                        # Generate a new output line
                        assert dest_block is not None, "delete_subsystems: dest_block not found"
                        new_output_line = SL_Line(src=src_block.name, dest=dest_block.name,
                                                  src_port=port_line.src_port, dest_port=output_line.dest_port)
                        new_output_line.name = output_line.name
                        # Delete the old line (output_line) and add a new one
                        dest_block.add_dest(output_line.dest_port, new_output_line)
                        # Add a new line for src_block
                        src_block.add_src(port_line.src_port, new_output_line)

        # Delete all the subsystems
        for name in subsystems:
            del self.blocks_dict[name]

        # Add new blocks from subsystems to block_dict
        for block in blocks_in_subsystems:
            assert block.name not in self.blocks_dict, "Repeated block name %s" % block.name
            self.blocks_dict[block.name] = block

    def connect_goto(self):
        """Connect from blocks with goto blocks."""
        from_blocks = dict()
        goto_blocks = dict()
        for _, block in self.blocks_dict.items():
            if block.type == "from":
                from_blocks[block.tag] = block
            if block.type == "goto":
                goto_blocks[block.tag] = block

        for tag, from_block in from_blocks.items():
            # For each from-block, find the corresponding goto block, the
            # destination of from-block, and source of goto-block
            goto_block = goto_blocks[tag]
            goto_line = goto_block.dest_lines[0]
            src_goto_block = self.blocks_dict[goto_line.src]

            from_line = from_block.src_lines[0][0]
            dest_from_block = self.blocks_dict[from_line.dest]

            src_goto_block.src_lines[goto_line.src_port][goto_line.branch] = unknownLine

            new_input_line = SL_Line(src=src_goto_block.name, dest=dest_from_block.name,
                                     src_port=goto_line.src_port, dest_port=from_line.dest_port)
            new_input_line.branch = goto_line.branch
            new_input_line.name = goto_line.name

            # Delete the old line (port_line) and add a new one
            dest_from_block.add_dest(from_line.dest_port, new_input_line)
            # Add a new line for src_block
            src_goto_block.add_src(goto_line.src_port, new_input_line)

            del self.blocks_dict[from_block.name]
            del self.blocks_dict[goto_block.name]

    def separate_diagram(self):
        """Separate the diagram into the different parts, and stored in the
        corresponding variables in self.

        """
        for _, block in self.blocks_dict.items():
            # Continuous and discrete blocks contain the field is_continuous
            if hasattr(block, "is_continuous"):
                if isinstance(block, Scope):
                    self.scopes.append(block)
                elif block.is_continuous:
                    self.continuous_blocks.append(block)
                else:
                    self.discrete_blocks.append(block)
            elif isinstance(block, DataStoreMemory):
                self.dsms.append(block)
            else:
                assert False, "block: %s" % type(block)
