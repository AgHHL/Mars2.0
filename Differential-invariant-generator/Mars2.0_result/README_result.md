# Mars2 Benchmark Subset

This file records the 2D benchmark subset used by this tool from Pegasus benchmark source `Pegasus-benchmark.rtf`.

## Source

- Original benchmark source: `Pegasus-benchmark.rtf`
- Local development path: `.../Mars2.0/Differential-invariant-generator/Pegasus_benchmark.rtf`

## Currently solved case IDs (from 1-70)

`1, 4, 5, 6, 11, 17, 21, 28, 29, 35, 37, 41, 48, 49, 50, 51, 52, 53, 55, 57, 58, 66, 68, 69`

## Figure mapping

For a solved case `k`, the script exports:

- `case-k.png`

Example:

- case 49 -> `case-49.png`
- case 50 -> `case-50.png`
- case 57 -> `case-57.png`

## Figure legend (how to read each `case-k.png`)

- Gray arrows: the vector field of the ODE (`x' = f(x)`), showing local flow direction.
- Black curves: sampled trajectories integrated from points in the initial set.
- Blue area: initial set `I(x) <= 0` (or an equivalent thin band for equality-defined initials).
- Red area: unsafe set `U(x) <= 0` (or an equivalent thin band for equality-defined unsafe sets).
- Light pink area: certified barrier region `B(x) <= 0`.
- Dashed/dotted pink boundary: the barrier boundary `B(x) = 0`.
- Axes labels: state variables used in that case (for example `x, y`).

Interpretation: a successful certificate means trajectories from the blue region are separated from the red region by the barrier constraints.

## Reproduction note

Set `caseNumbers` in `Pegasus_benchmark.wl` and run:

```bash
wolframscript -file Barrier_certificate_synthesis.wl
```

The parser reads benchmark blocks directly from `Pegasus-benchmark.rtf`, so case indexing must match the source file order.
