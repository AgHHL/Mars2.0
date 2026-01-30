from ss2hcsp.sysml_sm.sm_chart import SM_Chart
from ss2hcsp.sf.sf_chart import SF_Chart

def convert_sm_to_sf(sm_chart):
    # 提取 SM_Chart 的必要信息
    name = sm_chart.name
    state = sm_chart.diagram  # Assuming the `state` in SM_Chart is compatible with SF_Chart
    data = sm_chart.data
    num_src = sm_chart.num_src
    num_dest = sm_chart.num_dest
    st = sm_chart.st

    # 创建 SF_Chart 对象
    sf_chart = SF_Chart(name, state, data, num_src, num_dest, st)

    # 复制相关数据
    sf_chart.input_events = sm_chart.input_events  # 复制输入事件
    sf_chart.exec_name = sm_chart.exec_name  # 复制执行名称
    sf_chart.src_lines = sm_chart.src_lines  # 复制源线
    sf_chart.dest_lines = sm_chart.dest_lines  # 复制目标线
    sf_chart.port_to_in_var = sm_chart.port_to_in_var  # 复制输入端口变量映射
    sf_chart.port_to_out_var = sm_chart.port_to_out_var  # 复制输出端口变量映射
    sf_chart.all_vars = sm_chart.all_vars  # 复制所有变量

    return sf_chart
