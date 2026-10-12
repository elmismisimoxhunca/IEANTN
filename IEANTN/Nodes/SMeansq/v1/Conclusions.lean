/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import IEANTN.Vocabulary

/-!
# Node `SMeansq`

A **pipeline** node carrying a pointwise corridor and two window moment bounds to an explicit
short-interval mean-square bound on the zeta argument function `S`:

`∫_{T}^{T+H} S(t)^2 dt ≤ y^2 * H`,
`y = (√d1 + √(d1 + 4πΩr1)) / (2π)`,

where `d1` bounds the mean square of the smoothed-prime polynomial `D` on the window, `r1` bounds
the first moment of the remainder `R`, and `Ω` is a pointwise bound for `|S|` on the window.

The argument is the first-moment route of Selberg's smoothed explicit formula. The Lean proof
does not integrate the signed identity `π S² = -S D - S R`: `IntegrableOn (D^2)` makes `|D|`
measurable, not `D`. It integrates the pointwise bound `π S² ≤ |S| |D| + Ω |R|` and applies
Hölder with `p = q = 2`. With `u = √(∫ S²)` this gives `π u² ≤ u √(d1 H) + Ω r1 H`, and the
quadratic `π w² - √d1 w - Ω r1 ≤ 0` (for `u = w√H`) solves to `w ≤ y`. No pair-correlation input
is used anywhere: the remainder is controlled in *first* moment only, which is why the bound
reaches moderate heights rather than the very large heights explicit moment estimates need when
they take a genuine second moment of the remainder.

Everything analytic above the assembly — the existence of the decomposition (Selberg's smoothed
formula), the Beurling–Selberg majorant that diagonalizes `D`'s mean square, and the zero-count
first moment behind `r1` — arrives through the hypotheses. Follow-up nodes are expected for those
inputs; see the node metadata's limitations.

Provenance: this statement shape was derived outside the network (exhibit `msq_s`, 2026-08-20,
with erratum). It is an original result, not a transcription of a published theorem; see the
limitations on novelty.
-/

namespace SMeansq.v1

open IEANTN Real

/-- **Short-interval mean-square assembly.** Let `T`, `H` be real with `0 < H`, and suppose that on
the window `[T, T + H]`:

* the smoothed explicit-formula decomposition `π * S t = -(D t) - (R t)` holds;
* the pointwise corridor `|S t| ≤ Ω` holds, with `Ω ≥ 0`;
* `D` has mean square at most `d1 * H` and `R` has first moment at most `r1 * H`
  (both `d1, r1 ≥ 0`);

then `∫_{T}^{T+H} S(t)^2 dt ≤ y^2 * H` with
`y = (√d1 + √(d1 + 4πΩr1)) / (2π)`.

Every hypothesis imports nothing: `D` and `R` are arbitrary real functions and the moment bounds
are stated as given, so this conclusion is downstream of whatever nodes eventually supply the
decomposition and the two moment bounds. The interval of integration is half-open `Ioc`; the
decomposition and corridor are demanded on the closed window, which differs only by the endpoint.

The bound is deliberately not sharp: at `T ≈ 3·10^12`, `H = 10^4` the exhibited instantiation
gives `y² ≈ 7.62` against Selberg's asymptotic `≈ 0.17`, i.e. the point is explicitness and
moderate height, not sharpness.

**Integrability is part of the statement, on purpose.** Mathlib totalizes the Bochner integral
of nonintegrable functions to `0`; without integrability hypotheses the moment premises could be
satisfied vacuously (e.g. `D t = 1/(t - T)`, square-integral divergent in reality, `0` as a Lean
integral) while the conclusion is false. `D²` and `|R|` are therefore required to be integrable
on the window, which is exactly what the proof consumes via Cauchy–Schwarz. -/
def assembly : Prop :=
  ∀ (T H Ω d1 r1 : ℝ) (D R : ℝ → ℝ),
    0 < H → 0 ≤ Ω → 0 ≤ d1 → 0 ≤ r1 →
    (∀ t ∈ Set.Icc T (T + H), π * zetaS t = -(D t) - (R t)) →
    (∀ t ∈ Set.Icc T (T + H), |zetaS t| ≤ Ω) →
    MeasureTheory.IntegrableOn (fun t => (D t) ^ 2) (Set.Ioc T (T + H)) →
    MeasureTheory.IntegrableOn (fun t => |R t|) (Set.Ioc T (T + H)) →
    (∫ t in Set.Ioc T (T + H), (D t) ^ 2) ≤ d1 * H →
    (∫ t in Set.Ioc T (T + H), |R t|) ≤ r1 * H →
    (∫ t in Set.Ioc T (T + H), (zetaS t) ^ 2) ≤
      ((Real.sqrt d1 + Real.sqrt (d1 + 4 * π * Ω * r1)) / (2 * π)) ^ 2 * H

end SMeansq.v1
