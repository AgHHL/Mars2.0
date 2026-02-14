# Mars2 Barrier-Certificate-Style Dynamical Invariant Synthesis Tool

This repository contains a Wolfram Language implementation for barrier-certificate-style invariant synthesis on polynomial dynamical systems, using Pegasus benchmarks [5].

## Repository files

- `Barrier_certificate_synthesis.wl`: main solver script.
- `Pegasus_benchmark.rtf`: Pegasus benchmark source file (in local development this was `...Mars2.0/Differential-invariant-generator/Pegasus_benchmark.rtf`).
- File: `Mars2_result`: contains the successful synthesis results of our tool on 2D benchmark subset and note.
  - `case-k.png`: exported result figure for benchmark case `k`.
  - `README_result.md`: result details.

## 1. Synthesis process, methods, BC conditions, and hyperparameters

### 1.1 End-to-end synthesis pipeline

For each selected benchmark case:

1. Parse `ProgramVariables` and ODEs from the benchmark text.
2. Parse `initial`, `unsafe`, and optional `domain` constraints into
  - inequality set: `g(x) >= 0`
  - equality set: `h(x) == 0`
3. Build polynomial barrier template(s) `B(x)` (or `{B_1(x),...,B_m(x)}` for vector barrier certificate).
4. Build SOS constraints from initial/unsafe/Lie conditions.
5. Solve barrier certificate(BC) with five methods in sequence:
  - convex condition:
    - Exponential-type BC condition, including convex BC [1].
  - non-convex condition and use Local convexity method:
    - Invariant BC condition and Alternating Direction (AD) method [2,4]
    - Vector BC condition and AD method [3,4]
    - Invariant BC condition and Difference-of-Convex (DC) method [2]
    - Vector BC condition and DC method [2,3]
6. Run exact symbolic post-verification with `Reduce`.
7. Export figure and print verified barrier certificate if successful.

### 1.2 Single-barrier (Exponential-type [1] and Invariant BC [2]) conditions used in code

Let $\dot{x} = f(x)$, barrier $B(x)$, domain constraints $d_i(x) \ge 0$, $q_j(x) = 0$.
Let initial component constraints be $g_i^I(x) \ge 0$, $h_j^I(x) = 0$, and unsafe component constraints be $g_i^U(x) \ge 0$, $h_j^U(x) = 0$.

The SOS templates used are:

- Initial condition (for each initial component):

  $$
  -B(x) - \sum_i \sigma_i^I(x) g_i^I(x) + \sum_j p_j^I(x) h_j^I(x) - \varepsilon_I
  $$
  is SOS, with each $\sigma_i^I$ constrained to be SOS.

- Unsafe condition (for each unsafe component):

  $$
  B(x) - \sum_i \sigma_i^U(x) g_i^U(x) + \sum_j p_j^U(x) h_j^U(x) - \varepsilon_U
  $$
  is SOS, with each $\sigma_i^U$ constrained to be SOS.

- Lie condition (`LieOrder = 1` in current default setup):

  $$
  -L_f B(x) + v(x) B(x) - \sum_i \sigma_i^W(x) d_i(x) + \sum_j p_j^W(x) q_j(x) - \varepsilon_L
  $$
  is SOS, with each $\sigma_i^W$ constrained to be SOS.

In all three conditions:

- $\sigma(\cdot)$ are SOS multipliers (therefore globally nonnegative).
- $p(\cdot)$ are unconstrained polynomial multipliers for equality constraints (they are not required to be SOS).
- $v(\cdot)$ in the single-BC Lie condition is also an unconstrained polynomial multiplier, while it's taken as a user-defined parameter in Exponential-type BC, convexifying the synthesis problem [1].

Then symbolic verification checks:

- Initial set implies $B(x) \le 0$.
- $B(x) \le 0$ implies not unsafe.
- On domain (usually the boundary-chain conditions), Lie derivative condition holds, i.e. $B(x) = 0$ implies $L_fB(x) < 0$.

### 1.3 Vector-BC conditions used in code [3]

For $B_1, \ldots, B_m$(`m = 2` default):

- Initial: each $B_r$ must satisfy an SOS condition of the same style as single BC.
- Unsafe: code enforces an SOS condition on $\sum_r B_r$, and final symbolic verification requires
  $$
  \text{unsafe} \Rightarrow (B_1 > 0 \lor \cdots \lor B_m > 0).
  $$
- Lie: for each component,

  $$
  -L_f B_r(x) + \sum_{s=1}^m c_{r,s} B_s(x)
  - \sum_i \sigma^W_{r,i}(x)\, d_i(x)
  + \sum_j p^W_{r,j}(x)\, q_j(x)
  - \varepsilon_L
  $$
  is SOS,

  where:

  - $d_i(x) \ge 0$ and $q_j(x)=0$ are domain constraints.
  - $\sigma^W_{r,i}(x)$ are SOS multipliers and $p^W_{r,j}(x)$ are polynomial multipliers.
  - For the high-level Vector-BC design, we use positive off-diagonal coupling:
    $$
    c_{r,s} \ge 0 \quad (r \ne s),
    $$
    while diagonal terms $c_{r,r}$ are free design coefficients.

  The post-verification Lie condition is component-wise on active facets:

  $$
  \forall r,\quad
  \big(d_i(x)\ge 0,\ q_j(x)=0\ \forall i,j\big)
  \Rightarrow
  \Big(B_r(x)=0 \land \bigwedge_{k\ne r} B_k(x)\le 0\Big)
  \Rightarrow
  L_f B_r(x) < 0.
  $$

  This is the boundary-inward condition for the intersection safe set
  $\{x \mid B_1(x)\le 0,\ldots,B_m(x)\le 0\}$.

### 1.4 How BC Conditions Are Encoded as SDP (Implementation)

This section summarizes the implementation-level SDP encoding, including the auxiliary scalar $\lambda$.

- SOS-to-LMI conversion:
  each polynomial SOS constraint is converted to a coefficient-matching matrix inequality ($C_i \succeq 0$) on a canonical monomial basis.
- Numerical normalization:
  each LMI matrix is divided by the maximum absolute numeric constant appearing in that matrix before adding semidefinite-cone constraints.
- Feasibility objective:
  the solver optimizes an auxiliary scalar $\lambda$ (by maximizing $\lambda$) to enlarge feasibility margin, by constraining the (LMI matrix minus $\lambda I$) a positive definite matrix.
  $$
  C_i - \lambda I \succeq 0
  $$
- Box constraints on decision variables:
  polynomial and multiplier coefficients are constrained in a cuboid range (`paraRange`, default `[-1,1]`).
- Vector-coupling implementation:
  for off-diagonal couplings ($r \ne s$), the code uses an auxiliary diagonal block with
  $$
  \operatorname{diag}(c_{\text{off}}) - \lambda I \succeq 0,
  $$
  equivalent to $c_{r,s} \ge \lambda$ for all off-diagonal entries.
  So strict positivity ($c_{r,s}>0$) is achieved only when the optimized $\lambda$ is positive.

### 1.5 Five methods and exact role

| Method | ID in output tuple | Core idea |
|---|---|---|
| Exponential | 1 | Fix the polynomial $p$ as a scalar `c` in $-L_f B + vB...$ and solve convex SDP over candidate `c` values: $c \in \{ -1, -0.5, 0, 0.5, 1 \}$ [1]. |
| Invariant+AD | 2 | Alternating minimization on bilinear decision blocks, especially $v(s,x) \times B(a,x)$, using AD-style bilinear SOS handling [2,4]. |
| Vector+AD | 3 | Vector barrier template [3] with AD subsolver [4]. |
| Invariant+DC | 4 | Difference-of-convex iterative handling of BMI nonconvexity for invariant BC [2]. |
| Vector+DC | 5 | Vector barrier template [3] with DC-style nonconvex handling [2]. |

### 1.6 Hyperparameters currently used (default values in script)

Core synthesis parameters (`parseBenchmark`):

- `barrierDegree = 6` for 2D (`3` otherwise)
- `polyAddDegree = 3` for multiplier polynomial degree
- `paraRange = {-1, 1}`
- `epsilon_I = 0`
- `epsilon_U = epsilon_L = 1e-7` for the strict inequal constrains
- `epsilon_AM = epsilon_DC = epsilon_Vector = 1e-5` for local optimum termination
- `seed = 0`

Method iteration controls(We stochatically select the initial points for bilinear variable to solve a local optimum by seeds iteratively):
- AM: up to `5` seeds, `AMround = 20`
- DC: up to `5` seeds, `DCround = 20`
- Vector methods: up to `10` seeds, `vectorNum = 2`

SDP and runtime controls:

- SDP call hard timeout: `$SDPCallTimeLimit = 300` seconds
- Method call timeout (AM/DC): `$MethodCallTimeLimit = 600` seconds
- Vector method timeout: `$VectorMethodCallTimeLimit = 1200` seconds
- Setup stage budget per degree: `$SetupCallTimeLimit = 900` seconds
- Global per-case budget in `main`: `timebound = 3000` seconds
- SDP options:
  - primary: `MaxIterations -> 300`
  - fallback: `MaxIterations -> 1200`

### 1.7 Current 2D cases reported as solvable

From 2-Dims pegasus evaluation set (cases 1-70), successful cases of Mars2.0 include:

`1, 4, 5, 6, 11, 17, 21, 28, 29, 35, 37, 41, 48, 49, 50, 51, 52, 53, 55, 57, 58, 66, 68, 69`.

For the pegasus tool, it can solve these cases individually using barrier certificate(convex, exponential, vector types):

`1, 2, 4, 5, 9, 11, 13, 21, 23, 27, 28, 29, 32, 37, 40, 44, 45, 48, 49, 50, 51, 52, 53, 54, 55, 60, 63, 66, 67, 68, 69`.

What the cases we can solve rather the pegasus are:

`6, 17, 35, 41, 57, 58`.

What the cases pegasus can solve while Mars2.0 can't are:

`2, 9, 13, 23, 27, 32, 40, 44, 45, 54, 60, 63, 67`.

These differences mainly because of:
1. We use different hyperparametres.
2. Mars2.0 only use the SDP solver, while Pegasus use LP and SDP, maybe some cases can be solve by LP while SDP can't.
3. Mars2.0 consider the bilinear property cause by more expressive Lie conditions in invariant and vector BC, while Pegasus only consider the convex Lie conditions. So we can solve the cases that Pegasus can't. It is a trade-off in barrier certificate conditions between expression and efficiency.

## 2. How to use this code

### 2.1 Configure benchmark path and case list

At the end of `Barrier_certificate_synthesis.wl`, set:

```wl
filePath = "/path/to/Pegasus_benchmark.rtf";
caseNumbers = {1}; (*the testing list of case numbers*)
processFile[filePath, caseNumbers];
```

### 2.2 Run

From terminal:

```bash
wolframscript -file Barrier_certificate_synthesis.wl
```

You will see logs such as:

- benchmark definition
- method attempts by degree
- success/failure and `(degree, time, methodId)`
- exported figure path (`case-k.png`)
- verified barrier certificate (if found)

## 3. What is `Pegasus_benchmark.rtf` used for?

`Pegasus_benchmark.rtf` is the raw benchmark source from Pegasus [5].

This script reads it as plain text and extracts each benchmark block:

- `ProgramVariables ... End.`
- `Problem ... End.`

Then it converts constraints and ODEs into symbolic WL expressions for SOS construction and symbolic verification.

Important behavior for parameterized cases:

- If extra symbols appear that are not state variables, the script tries to eliminate them using equalities in initial conditions.
- If unresolved parameters remain, the case is marked unsupported with:
  `{"UnsupportedParameterCase", {...}}`.

## 4. Running in VSCode: prerequisites and setup

### 4.1 Required software

- Wolfram Mathematica or Wolfram Engine installed.
- `wolframscript` available in PATH.
  - quick check: `wolframscript -version`

### 4.2 Recommended VSCode setup

- Install a Wolfram Language extension (for syntax highlighting and optional language server).
- Open this folder as a workspace.
- Edit `Barrier_certificate_synthesis.wl` directly.

### 4.3 Running from VSCode terminal

Use the integrated terminal:

```bash
cd /path/to/this/repo
wolframscript -file Barrier_certificate_synthesis.wl
```

### 4.4 Figure output behavior

By default, non-FrontEnd runs export figures as:

- `case-1.png`, `case-2.png`, ...

in the script directory (`$WolframScriptImageDir = Automatic`).

If needed, you can adjust:

- `$WolframScriptOpenImages`
- `$WolframScriptImageDir`
- `$WolframScriptImageFormat`

## 5. References

- [1] Hui Kong, Fei He, Xiaoyu Song, William N. N. Hung, and Ming Gu. 2013.
  Exponential-Condition-Based Barrier Certificate Generation for Safety Verification of Hybrid Systems.
  In *CAV 2013* (LNCS, Vol. 8044). Springer, 242-257.
  DOI: [10.1007/978-3-642-39799-8_17](https://doi.org/10.1007/978-3-642-39799-8_17)

- [2] Qiuye Wang, Mingshuai Chen, Bai Xue, Naijun Zhan, and Joost-Pieter Katoen. 2022.
  Encoding inductive invariants as barrier certificates: Synthesis via difference-of-convex programming.
  *Information and Computation* 289, Part (2022), 104965.
  DOI: [10.1016/J.IC.2022.104965](https://doi.org/10.1016/J.IC.2022.104965)

- [3] Andrew Sogokon, Khalil Ghorbal, Yong Kiam Tan, and Andre Platzer. 2018.
  Vector Barrier Certificates and Comparison Systems.
  In *FM 2018* (LNCS, Vol. 10951). Springer, 418-437.
  DOI: [10.1007/978-3-319-95582-7_25](https://doi.org/10.1007/978-3-319-95582-7_25)

- [4] Zhengfeng Yang, Wang Lin, and Min Wu. 2015.
  Exact Safety Verification of Hybrid Systems Based on Bilinear SOS Representation.
  *ACM Transactions on Embedded Computing Systems* 14, 1 (2015), 16:1-16:19.
  DOI: [10.1145/2629424](https://doi.org/10.1145/2629424)

- [5] Andrew Sogokon, Stefan Mitsch, Yong Kiam Tan, Katherine Cordwell, and Andre Platzer. 2021.
  Pegasus: sound continuous invariant generation.
  *Formal Methods in System Design* 58, 1-2 (2021), 5-41.
  DOI: [10.1007/S10703-020-00355-Z](https://doi.org/10.1007/S10703-020-00355-Z)

## Notes

- This repository is intended for reproducible tool-paper experiments.
- Keep benchmark file, case list, and generated figures under version control for exact reproducibility.
