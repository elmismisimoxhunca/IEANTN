/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import IEANTN.Nodes.SMeansq.v1.Conclusions

/-!
# Examples: `SMeansq.v1`

One consequence per conclusion, taken as a hypothesis, to show what the statement buys. The
hypotheses of `assembly` are heavy — that is the design: they are the future nodes. The example
instantiates the assembly at a symbolic window and reads off the shape of the conclusion.
-/

namespace SMeansq.v1.Examples

open Real

/-- On any window where the decomposition, corridor and moment bounds hold, the mean square of
`S` over the window is at most `y^2 * H`. This is the statement a consumer of the node would use:
bound the two moment inputs and the corridor, and the window estimate falls out. -/
example (h : SMeansq.v1.assembly)
    (T H Ω d1 r1 : ℝ) (D R : ℝ → ℝ)
    (hH : 0 < H) (hΩ : 0 ≤ Ω) (hd1 : 0 ≤ d1) (hr1 : 0 ≤ r1)
    (hdec : ∀ t ∈ Set.Icc T (T + H), π * IEANTN.zetaS t = -(D t) - (R t))
    (hcor : ∀ t ∈ Set.Icc T (T + H), |IEANTN.zetaS t| ≤ Ω)
    (hDint : MeasureTheory.IntegrableOn (fun t => (D t) ^ 2) (Set.Ioc T (T + H)))
    (hRint : MeasureTheory.IntegrableOn (fun t => |R t|) (Set.Ioc T (T + H)))
    (hD : (∫ t in Set.Ioc T (T + H), (D t) ^ 2) ≤ d1 * H)
    (hR : (∫ t in Set.Ioc T (T + H), |R t|) ≤ r1 * H) :
    (∫ t in Set.Ioc T (T + H), (IEANTN.zetaS t) ^ 2) ≤
      ((Real.sqrt d1 + Real.sqrt (d1 + 4 * π * Ω * r1)) / (2 * π)) ^ 2 * H :=
  h T H Ω d1 r1 D R hH hΩ hd1 hr1 hdec hcor hDint hRint hD hR

/-- The trivial corner: with `Ω = d1 = r1 = 0` the bound forces `y = 0`, so the mean square
vanishes — a sanity check that the constants are not hiding a positive floor. (Of course a
window on which `|S| ≤ 0` and both moment bounds vanish is not expected to exist; the example
only checks that the algebra degenerates honestly.) -/
example (h : SMeansq.v1.assembly)
    (T H : ℝ) (D R : ℝ → ℝ)
    (hH : 0 < H)
    (hdec : ∀ t ∈ Set.Icc T (T + H), π * IEANTN.zetaS t = -(D t) - (R t))
    (hcor : ∀ t ∈ Set.Icc T (T + H), |IEANTN.zetaS t| ≤ 0)
    (hDint : MeasureTheory.IntegrableOn (fun t => (D t) ^ 2) (Set.Ioc T (T + H)))
    (hRint : MeasureTheory.IntegrableOn (fun t => |R t|) (Set.Ioc T (T + H)))
    (hD : (∫ t in Set.Ioc T (T + H), (D t) ^ 2) ≤ 0 * H)
    (hR : (∫ t in Set.Ioc T (T + H), |R t|) ≤ 0 * H) :
    (∫ t in Set.Ioc T (T + H), (IEANTN.zetaS t) ^ 2) ≤ 0 := by
  have := h T H 0 0 0 D R hH (le_refl _) (le_refl _) (le_refl _) hdec hcor hDint hRint hD hR
  simpa using this

end SMeansq.v1.Examples
