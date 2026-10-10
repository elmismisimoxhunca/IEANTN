/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.SMeansq.v1.Conclusions

/-!
# Solution: `SMeansq.v1`

Proves the same declarations `Challenge.lean` states. Does not import the challenge module.

The argument runs through absolute values throughout. Integrability of `D²` and `|R|` makes `|D|`
and `|R|` a.e.-measurable but says nothing about the signs of `D` and `R`, so `S * D` need not be
measurable. The pointwise bound `π S² ≤ |S| |D| + Ω |R|` on the window avoids the signs, and
Cauchy–Schwarz is applied to `|S|` and `|D|`. If `S²` is not integrable on the window, its integral
is `0` and the bound is trivial; otherwise `|S| = √(S²)` is a.e.-measurable as well.
-/

open MeasureTheory Real

namespace SMeansq.v1.Dev

/-- The quadratic step: `π u² ≤ u √(d1 H) + c H` forces `u² ≤ y² H`. -/
theorem quadratic_step {I H d1 c : ℝ} (hH : 0 < H) (hI : 0 ≤ I) (hd1 : 0 ≤ d1) (hc : 0 ≤ c)
    (h : π * I ≤ √I * √(d1 * H) + c * H) :
    I ≤ ((√d1 + √(d1 + 4 * π * c)) / (2 * π)) ^ 2 * H := by
  set u := √I
  set s := √H
  set a := √d1
  set r := √(d1 + 4 * π * c)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hs0 : 0 < s := Real.sqrt_pos.mpr hH
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have huu : u ^ 2 = I := Real.sq_sqrt hI
  have hss : s ^ 2 = H := Real.sq_sqrt hH.le
  have haa : a ^ 2 = d1 := Real.sq_sqrt hd1
  have hrr : r ^ 2 = d1 + 4 * π * c := Real.sq_sqrt (by positivity)
  have hdH : √(d1 * H) = a * s := Real.sqrt_mul hd1 H
  rw [hdH, ← huu, ← hss] at h
  have hpi := Real.pi_pos
  have key : 2 * π * u - a * s ≤ r * s := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hrs : 0 ≤ r * s := mul_nonneg hr0 hs0.le
    have hsq := mul_self_lt_mul_self hrs hlt
    nlinarith
  have hu_le : u ≤ (a + r) / (2 * π) * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  rw [← huu, ← hss, ← mul_pow]
  exact pow_le_pow_left₀ hu0 hu_le 2

/-- Square-integrability makes `|h| = √(h²)` a.e.-measurable, though not `h` itself. -/
theorem aestronglyMeasurable_abs {μ : Measure ℝ} {h : ℝ → ℝ}
    (hh : Integrable (fun t => h t ^ 2) μ) : AEStronglyMeasurable (fun t => |h t|) μ := by
  have := Real.continuous_sqrt.comp_aestronglyMeasurable hh.aestronglyMeasurable
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs] using this

/-- Cauchy–Schwarz for the absolute values of two functions whose squares are integrable. Only
`|f|` and `|g|` need be measurable, which is all that square-integrability provides. -/
theorem integral_abs_mul_abs_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun t => f t ^ 2) μ) (hg : Integrable (fun t => g t ^ 2) μ) :
    ∫ t, |f t| * |g t| ∂μ ≤ √(∫ t, f t ^ 2 ∂μ) * √(∫ t, g t ^ 2 ∂μ) := by
  have habs : ∀ {h : ℝ → ℝ}, Integrable (fun t => h t ^ 2) μ →
      MemLp (fun t => |h t|) (ENNReal.ofReal 2) μ := by
    intro h hh
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq (aestronglyMeasurable_abs hh)]
    simpa only [sq_abs] using hh
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t => abs_nonneg (f t))
    (Filter.Eventually.of_forall fun t => abs_nonneg (g t)) (habs hf) (habs hg)
  simpa only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs

theorem assembly : SMeansq.v1.assembly := by
  intro T H Ω d1 r1 D R hH hΩ hd1 hr1 hdec hcor hD hR hD1 hR1
  set y := (√d1 + √(d1 + 4 * π * Ω * r1)) / (2 * π)
  have hrhs : 0 ≤ y ^ 2 * H := by positivity
  by_cases hS : IntegrableOn (fun t => IEANTN.zetaS t ^ 2) (Set.Ioc T (T + H))
  swap
  · rw [integral_undef hS]
    exact hrhs
  set μ := volume.restrict (Set.Ioc T (T + H))
  have hwin : ∀ᵐ t ∂μ, t ∈ Set.Icc T (T + H) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Set.Ioc_subset_Icc_self ht
  -- pointwise: `π S² = -S D - S R ≤ |S| |D| + Ω |R|`
  have hpt : ∀ᵐ t ∂μ,
      π * IEANTN.zetaS t ^ 2 ≤ |IEANTN.zetaS t| * |D t| + Ω * |R t| := by
    filter_upwards [hwin] with t ht
    have h1 := hdec t ht
    have h2 := hcor t ht
    calc π * IEANTN.zetaS t ^ 2 = -(IEANTN.zetaS t * D t) - IEANTN.zetaS t * R t := by
          linear_combination IEANTN.zetaS t * h1
      _ ≤ |IEANTN.zetaS t * D t| + |IEANTN.zetaS t * R t| := by
          linarith [neg_le_abs (IEANTN.zetaS t * D t), neg_le_abs (IEANTN.zetaS t * R t)]
      _ ≤ |IEANTN.zetaS t| * |D t| + Ω * |R t| := by
          rw [abs_mul, abs_mul]
          gcongr
  have hSD : Integrable (fun t => |IEANTN.zetaS t| * |D t|) μ := by
    refine Integrable.mono' ((hS.add hD).div_const 2) ?_ ?_
    · exact (aestronglyMeasurable_abs hS).mul (aestronglyMeasurable_abs hD)
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs, Pi.add_apply]
      nlinarith [sq_nonneg (|IEANTN.zetaS t| - |D t|), sq_abs (IEANTN.zetaS t), sq_abs (D t)]
  have hint : π * (∫ t, IEANTN.zetaS t ^ 2 ∂μ) ≤
      (∫ t, |IEANTN.zetaS t| * |D t| ∂μ) + Ω * ∫ t, |R t| ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hSD (hR.const_mul Ω)]
    exact integral_mono_ae (hS.const_mul π) (hSD.add (hR.const_mul Ω)) hpt
  have hcs := integral_abs_mul_abs_le hS hD
  have hfin : π * (∫ t, IEANTN.zetaS t ^ 2 ∂μ) ≤
      √(∫ t, IEANTN.zetaS t ^ 2 ∂μ) * √(d1 * H) + (Ω * r1) * H := by
    have h3 : √(∫ t, D t ^ 2 ∂μ) ≤ √(d1 * H) := Real.sqrt_le_sqrt hD1
    have h4 : Ω * ∫ t, |R t| ∂μ ≤ Ω * (r1 * H) := mul_le_mul_of_nonneg_left hR1 hΩ
    have h5 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg (∫ t, IEANTN.zetaS t ^ 2 ∂μ))
    linarith
  have hq := quadratic_step hH (integral_nonneg fun t => sq_nonneg _) hd1 (mul_nonneg hΩ hr1) hfin
  simpa only [y, mul_assoc] using hq

end SMeansq.v1.Dev

theorem SMeansq.v1.challenge_assembly : SMeansq.v1.assembly :=
  SMeansq.v1.Dev.assembly

#print axioms SMeansq.v1.challenge_assembly
