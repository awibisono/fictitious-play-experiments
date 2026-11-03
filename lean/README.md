# Lean formalization

This directory accompanies work on **Arbitrarily Slow Polynomial Convergence of
Fictitious Play**, by Jacob Abernethy, John Lazarsfeld, and Andre Wibisono
([arXiv:2610.08768](https://arxiv.org/abs/2610.08768)). The paper constructs
zero-sum games with arbitrarily slow polynomial convergence of fictitious play.
The formal development includes refinements beyond the first arXiv version;
the Lean statements below specify its exact scope.

## Scope

- [`FaithfulMain.main_theorem`](Karlin/FaithfulMain.lean): the RPS-based recursive
  family with `(k + 1)^2 - 5` actions for every `k ≥ 2`.
- [`FaithfulSevenFamily.main_theorem`](Karlin/FaithfulSevenFamily.lean): an
  additional family with `(k + 1)^2 - 9` actions for every `k ≥ 3`.

These rational skew-symmetric games start from zero counts with a prescribed
common setup action. All subsequent simultaneous best responses are unique.
Their setup-inclusive empirical duality gap has a positive exact leading
constant times `t^(-1/k)`, with relative error `O(t^(-1/k))` as integer time
tends to infinity. The proofs include the seeds, recursive lift, and trajectory
realization. Computational results use verified realizers, supplied for both
families; they do not assert practical runtime bounds. The separate Python
experiments are not certified by these Lean proofs.

## Reproduce the verification

Install Python 3, Git, Bash, and [elan](https://github.com/leanprover/elan), with
`elan` and `lake` on your `PATH`. Network access is needed to obtain the pinned
Lean and mathlib dependencies. From the repository root:

```sh
cd lean
elan toolchain install leanprover/lean4:v4.27.0
python3 VERIFY_PACKAGE.py
bash REPRODUCE.sh
```

The script checks source integrity, builds with Lean 4.27.0 and the dependency
revisions in `lake-manifest.json`, and runs six independent probes and eight
companion checks. Logs and `result.json` are written to `reproduction-output/`.
For another run, supply a new output directory, for example
`bash REPRODUCE.sh /tmp/karlin-check-2`.

