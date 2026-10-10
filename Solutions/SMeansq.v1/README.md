# Solution: `SMeansq.v1`

Proves `SMeansq.v1.challenge_assembly : SMeansq.v1.assembly` in `Solution.lean`. The file has no
`sorry`, `admit`, `axiom` or `native_decide`, and imports only `IEANTN.Nodes.SMeansq.v1.Conclusions`.
It does not import the challenge.

## Status

- `lake build` in this directory: exit 0.
- `#print axioms SMeansq.v1.challenge_assembly`: `[propext, Classical.choice, Quot.sound]`.
- The `pp.all` statement-equality check in `docs/NODES.md` (challenge vs. solution `#check`):
  identical.
- `python scripts/ieantn.py progress SMeansq.v1`: typechecks, 0 declarations using `sorry`,
  `challenge_assembly` proved.
- Comparator: **not yet run**. It runs on the maintainer side, so the node's justification stays
  `none-yet` until a receipt exists.

## The argument

Write `S = zetaS` and `μ` for Lebesgue measure on `Ioc T (T + H)`.

1. If `S²` is not integrable on the window, Mathlib's integral is `0`, and `0 ≤ y² H`.
2. Otherwise, on the window (which lies inside the closed window `Icc` where the hypotheses
   hold), `π S² = -S D - S R ≤ |S| |D| + Ω |R|`.
3. Integrating gives `π ∫ S² ≤ ∫ |S| |D| + Ω ∫ |R|`. Hölder with `p = q = 2`
   (`integral_mul_le_Lp_mul_Lq_of_nonneg`) gives `∫ |S| |D| ≤ √(∫ S²) √(∫ D²)`. With the two
   moment hypotheses this becomes `π I ≤ √I √(d1 H) + Ω r1 H`, where `I = ∫ S²`.
4. `quadratic_step` turns this into `I ≤ y² H`, where
   `y = (√d1 + √(d1 + 4πΩ r1)) / (2π)`.

**Why absolute values.** `IntegrableOn (D²)` and `IntegrableOn |R|` make `|D| = √(D²)` and `|R|`
a.e.-measurable. They say nothing about the signs of `D` and `R`, so `D`, `R` and `S * D` need not
be measurable, and `π ∫ S² = -∫ S D - ∫ S R` is not available as written. Step 2 removes the signs
before integrating. Once `S²` is integrable, `|S| = √(S²)` is a.e.-measurable, and that is all the
proof uses. No measurability fact about `zetaS` itself is needed.

## Building

This directory is its own Lake project, with a path dependency on the repository root (same pattern
as `Solutions/PrimeInterval.v1`). `lean-toolchain` and the package revisions in
`lake-manifest.json` match the root.

```bash
cd Solutions/SMeansq.v1
lake exe cache get
lake build
```

To avoid fetching Mathlib over the network, first populate `.lake/packages/` with local
`git clone`s of the root's `.lake/packages/*`, each checked out at its manifest `rev` and with
`origin` set to the manifest URL. `lake exe cache get` then only decompresses from the local
Mathlib cache.
