# hhlpar
## Test cases
There is a list of test cases in function 'testSyncPostBoth' in class 'AssnTest' in 'assn_test.py'.<br> 
We can see the results of these cases by running:
```
>>>python -m unittest hhlpar.assn_test.AssnTest.testSyncPostBoth
```
## How to verify a HCSP process
We use function sync_mult to generate the assertions of processes and use function sync_post_both to verify properties from assertions. 
A single process must be written in form of HCSP for a simple example "{ y:=y+1;}* x:=y;". A parallel process should be written in a triple like (part1, part2, part3), where part2 is a dictionary recording the set of communicating channels, part1 (and part3) can also be single or parallel as a subprocess. If it is parallel, then its type is a triple. Otherwise, it is a dictionary, using "pn" to record a process name(A,B,C), using "P" to record HCSP. For parallel processes, all variables will be prefixed with the process name in assertions and conditions or invariants we provide.

After that we can verify the properties of the condition on the end state(Post) or the condition on all the continuous intervals(Postr) under the condition on initial state(Pre). In the simple example, when the process start with a state satisfying "y>0"(Pre), the end state will have "x>0"(Post). For this example, we need to provide loop invariant "y>0". Thus, we set "RI":[("R1","y>0")], where "R1" is the rec variable in assertion. If the function returns True, it means this property is verified. Sometimes, we need to provide differential invariants and methods with ODE recorded in "OI".

## Introduction of the case CCS 
The dictionary in line 311-333 from 'assn_test.py' shows the case of CCS:
* "PA" records the parallel process in the form of a triple:
  1. The first part is the plant process: "pn" gives a name "A" and "P" records the HCSP which contains a repetition of ODE interrupted by a communication, we use p_dot to denote derivate of p
  2. The second part uses "chset" to record the set of communicating channels
  3. The third part is the control process: "pn" gives a name "B" and "P" records the HCSP which contains a repetition of computing the acceleration
* "Pre" records the condition on the initial state
* "Post" records the condition on the end state to be proved
* "Postr" records the condition on all the continuous intervals to be proved
* "RI" records the loop invariant we provide
