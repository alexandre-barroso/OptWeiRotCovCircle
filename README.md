# Verification

Python 3.12.3; numpy 2.4.4; scipy 1.17.1; sympy 1.14.0; matplotlib 3.10.9. Lean 4.32.2; mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`. WolframScript 15.0.1 with a valid license.

```sh
python3 -B verify.py --all --output results
```

Do not use Python `-O`. The command checks Python calculations, compiles Lean, audits axioms, replays the compatible kernel and runs Wolfram; failures exit nonzero. Outputs go to `results`. No protected inputs are required.

Lean covers the covering optimum, full function-class envelope, reflection, continuity and finite controls. Formal dependencies are limited to propext, Classical.choice and Quot.sound.
