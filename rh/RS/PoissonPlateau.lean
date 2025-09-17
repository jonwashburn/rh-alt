/-
  rh/RS/PoissonPlateau.lean

  Poisson plateau for the normalized half-plane kernel
    P_b(y) = (1/π) * b / (y^2 + b^2).

  We fix the even window ψ := (1/4)·1_{[-2,2]} and prove a uniform plateau:
    (P_b * ψ)(x) ≥ c0  for all 0 < b ≤ 1 and |x| ≤ 1,
  with the explicit constant  c0 = 1/(4π).

  Mechanical measure-theory cleanup only; no new ideas.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Algebra.Group.Indicator
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Support

noncomputable section

namespace RH
namespace RS

open Set MeasureTheory
open scoped MeasureTheory

/-! ## Normalized Poisson kernel -/

/-- Normalized half-plane Poisson kernel on ℝ:
  `poissonKernel b y = (1/π) * b / (y^2 + b^2)`. -/
@[simp] def poissonKernel (b y : ℝ) : ℝ := (1 / Real.pi) * b / (y^2 + b^2)

lemma poissonKernel_nonneg (b : ℝ) (hb : 0 < b) (y : ℝ) : 0 ≤ poissonKernel b y := by
  have hpos : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
  have hden : 0 < y * y + b * b :=
    add_pos_of_nonneg_of_pos (mul_self_nonneg y) (mul_self_pos.mpr (ne_of_gt hb))
  have hfrac : 0 ≤ b / (y * y + b * b) := div_nonneg (le_of_lt hb) (le_of_lt hden)
  have hmul : 0 ≤ (1 / Real.pi) * (b / (y * y + b * b)) := mul_nonneg hpos hfrac
  have : 0 ≤ ((1 / Real.pi) * b) / (y * y + b * b) := by
    simpa [mul_div_assoc] using hmul
  simpa [poissonKernel, pow_two, mul_comm, mul_left_comm, mul_assoc] using this

/-- Nonnegativity of the normalized half‑plane Poisson kernel. -/
lemma halfplane_poisson_kernel_nonneg {b x : ℝ} (hb : 0 < b) :
  0 ≤ poissonKernel b x :=
  poissonKernel_nonneg b hb x

/-! ## The fixed window ψ := (1/4)·1_{[-2,2]} -/

/-- Simple even, nonnegative bump with unit mass and compact support:
    `ψ(t) = (1/4) · 1_{[-2,2]}(t)`. -/
@[simp] def psi (t : ℝ) : ℝ :=
  (1 / (4 : ℝ)) * Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1 : ℝ)) t

lemma psi_even : Function.Even psi := by
  classical
  intro t
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have hneg : -t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨hL, hR⟩
      constructor
      · have : -2 ≤ -t := by have := neg_le_neg hR; simpa using this
        exact this
      · have : -t ≤ 2 := by have := neg_le_neg hL; simpa using this
        exact this
    simp [psi, Set.indicator_of_mem, ht, hneg, mul_comm, mul_left_comm, mul_assoc]
  · have hneg : -t ∉ Icc (-2 : ℝ) 2 := by
      by_contra hmem
      -- If -t ∈ Icc(-2,2) then t ∈ Icc(-2,2)
      rcases hmem with ⟨hL, hR⟩
      have : t ∈ Icc (-2 : ℝ) 2 := by
        constructor
        · have := neg_le_neg hR; simpa using this
        · have := neg_le_neg hL; simpa using this
      exact ht this
    simp [psi, Set.indicator_of_not_mem, ht, hneg, mul_comm, mul_left_comm, mul_assoc]

lemma psi_nonneg : ∀ x, 0 ≤ psi x := by
  intro x
  classical
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · simp [psi, Set.indicator_of_mem, hx]
  · simp [psi, Set.indicator_of_not_mem, hx]

/-- Compute the (measure-theoretic) support `{x | ψ x ≠ 0}` of `ψ`: it is exactly `[-2,2]`. -/
lemma psi_support_eq : Function.support psi = Icc (-2 : ℝ) 2 := by
  classical
  ext x
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · simp [Function.support, psi, Set.indicator_of_mem, hx]
  · simp [Function.support, psi, Set.indicator_of_not_mem, hx]

/-- Compact support of `ψ` without deprecated constructors: identify `tsupport ψ`
    with `Icc (-2,2)` using `isClosed_Icc.closure_eq`. -/
lemma psi_hasCompactSupport : HasCompactSupport psi := by
  classical
  -- `HasCompactSupport ψ` reduces to compactness of `tsupport ψ`.
  change IsCompact (tsupport psi)
  -- `tsupport ψ = closure (Function.support ψ) = Icc (-2) 2`.
  have : tsupport psi = Icc (-2 : ℝ) 2 := by
    simpa [tsupport, psi_support_eq, isClosed_Icc.closure_eq]
  simpa [this] using isCompact_Icc

/-- Unit mass of `ψ` using `volume` and the interval-measure formula. -/
lemma psi_integral_one : ∫ x, psi x ∂(volume) = (1 : ℝ) := by
  classical
  have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
  calc
    ∫ x, psi x ∂(volume)
        = (1/4 : ℝ) * ∫ x, Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1 : ℝ)) x ∂(volume) := by
              simp [psi, mul_comm, mul_left_comm, mul_assoc]
    _   = (1/4 : ℝ) * ∫ x in Icc (-2 : ℝ) 2, (1 : ℝ) ∂(volume) := by
              simpa [hmeas] using
                (integral_indicator (s := Icc (-2 : ℝ) 2) (f := fun _ : ℝ => (1 : ℝ)))
    _   = (1/4 : ℝ) * (volume (Icc (-2 : ℝ) 2)).toReal := by
              simpa using (integral_const (s := Icc (-2 : ℝ) 2) (c := (1 : ℝ)))
    _   = (1/4 : ℝ) * (4 : ℝ) := by
              have hx : (-2 : ℝ) ≤ 2 := by norm_num
              have hμ : volume (Icc (-2 : ℝ) 2) = ENNReal.ofReal (2 - (-2)) := by
                simpa [hx, sub_neg_eq_add] using (measure_Icc (-2 : ℝ) 2)
              simpa [hμ, ENNReal.toReal_ofReal, sub_neg_eq_add, one_add_one_eq_two]
    _   = (1 : ℝ) := by ring

/-! ## Plateau: uniform lower bound for the Poisson average with ψ -/

/-- Poisson plateau with the fixed even window `ψ := (1/4)·1_{[-2,2]}`.
    We produce the explicit constant `c0 = 1/(4π)` valid for all `0 < b ≤ 1` and `|x| ≤ 1`. -/
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ x, 0 ≤ ψ x) ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x ∂(volume) = (1 : ℝ)) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, RH.RS.poissonKernel b (x - t) * ψ t ∂(volume)) ≥ c0 := by
  classical
  -- Fix ψ
  refine ⟨psi, psi_even, psi_nonneg, psi_hasCompactSupport, psi_integral_one, ?_⟩
  -- Choose explicit c0
  refine ⟨(1 / (4 * Real.pi)), ?_, ?_⟩
  · have hπ : 0 < Real.pi := Real.pi_pos
    have : 0 < 4 * Real.pi := by have : (0 : ℝ) < (4 : ℝ) := by norm_num; exact mul_pos this hπ
    simpa [one_div] using (one_div_pos.mpr this)
  · intro b x hb hb_le hx
    have hπ : 0 < Real.pi := Real.pi_pos
    have hb0 : 0 ≤ b := le_of_lt hb

    -- Rewrite the convolution using the indicator of [-2,2].
    have hmeas2 : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
    have conv_eq :
        (∫ t, poissonKernel b (x - t) * psi t ∂(volume))
          = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
      simp [psi, hmeas2, mul_comm, mul_left_comm, mul_assoc, integral_indicator]

    -- A single subinterval J := [x-b, x+b] sits inside [-2,2] if |x| ≤ 1 and b ≤ 1.
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      rcases abs_le.mp hx with ⟨hL, hR⟩
      exact ⟨by linarith, by linarith⟩
    have J_subset : Icc (x - b) (x + b) ⊆ Icc (-2 : ℝ) 2 := by
      intro t ht
      have hLx : -2 ≤ x := by linarith [hxIcc.1]
      have hRx : x ≤ 2 := by linarith [hxIcc.2]
      have hLb : -2 ≤ x - b := by linarith [hLx, hb_le]
      have hRb : x + b ≤ 2 := by linarith [hRx, hb_le]
      exact ⟨le_trans hLb ht.1, le_trans ht.2 hRb⟩

    -- Pointwise lower bound on J: |x-t| ≤ b ⇒ P_b(x - t) ≥ 1/(2π b).
    have kernel_lower_on_J :
        ∀ {t}, t ∈ Icc (x - b) (x + b) →
          poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b)) := by
      intro t ht
      -- |x - t| ≤ b on J
      have hdist : |x - t| ≤ b := by
        have h01 : -b ≤ t - x := by linarith [ht.1]
        have h02 : t - x ≤ b := by linarith [ht.2]
        have : |t - x| ≤ b := abs_le.mpr ⟨by linarith, by linarith⟩
        simpa [abs_sub_comm] using this
      -- Denominator comparison: (x-t)^2 + b^2 ≤ 2 b^2
      have hbne : b ≠ 0 := ne_of_gt hb
      have sq_le : (x - t)^2 ≤ b^2 := by
        have : |x - t|^2 ≤ b^2 := by
          have : 0 ≤ |x - t| := abs_nonneg _
          simpa [pow_two] using (mul_le_mul_of_nonneg_left hdist this)
        simpa [pow_two, sq_abs] using this
      have den_le : (x - t)^2 + b^2 ≤ 2 * b^2 := by
        have := add_le_add_right sq_le b^2
        simpa [two_mul] using this
      have den_pos : 0 < (x - t)^2 + b^2 := by
        have : 0 < b^2 := sq_pos_iff.mpr hbne
        exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
      have inv_lower :
          (1 : ℝ) / (2 * b^2) ≤ (1 : ℝ) / ((x - t)^2 + b^2) := by
        -- Using 0 < (x - t)^2 + b^2 and (x - t)^2 + b^2 ≤ 2*b^2
        exact one_div_le_one_div_of_le den_pos den_le
      -- Multiply by b > 0 and by (1/π) ≥ 0.
      have : b * (1 / (2 * b^2)) ≤ b * (1 / ((x - t)^2 + b^2)) :=
        mul_le_mul_of_nonneg_left inv_lower (le_of_lt hb)
      have hπ_nonneg : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt hπ)
      have : (1 / Real.pi) * (b * (1 / (2 * b^2)))
              ≤ (1 / Real.pi) * (b * (1 / ((x - t)^2 + b^2))) :=
        mul_le_mul_of_nonneg_left this hπ_nonneg
      -- Rewrite both sides to the Poisson kernel form
      have : (1 / (2 * Real.pi * b)) ≤ (1 / Real.pi) * (b / ((x - t)^2 + b^2)) := by
        -- left: (1/π) * (b / (2 b^2)) = 1/(2π b)
        simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
               one_div, pow_two] using this
      -- Flip to get the desired direction.
      exact this

    -- (1) Integral over [-2,2] ≥ integral over J by monotonicity & nonnegativity.
    have nonneg_pb : ∀ t, 0 ≤ poissonKernel b (x - t) := by
      intro t; simpa using halfplane_poisson_kernel_nonneg (x := x - t) hb
    have int_mono :
        ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume)
        ≥ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) := by
      -- Boundedness on finite intervals gives integrability.
      have bound : ∀ t, poissonKernel b (x - t) ≤ (1 / (Real.pi * b)) := by
        intro t
        have hb2pos : 0 < b^2 := sq_pos_iff.mpr (ne_of_gt hb)
        have den_pos : 0 < (x - t)^2 + b^2 :=
          add_pos_of_nonneg_of_pos (by exact sq_nonneg _) hb2pos
        have den_ge : b^2 ≤ (x - t)^2 + b^2 := by
          have : 0 ≤ (x - t)^2 := sq_nonneg _
          linarith
        have inv_le : 1 / ((x - t)^2 + b^2) ≤ 1 / b^2 := by
          have hb2pos : 0 < b^2 := sq_pos_iff.mpr (ne_of_gt hb)
          exact one_div_le_one_div_of_le hb2pos den_pos den_ge
        have : b * (1 / ((x - t)^2 + b^2)) ≤ b * (1 / b^2) :=
          mul_le_mul_of_nonneg_left inv_le (le_of_lt hb)
        have hπ_nonneg : 0 ≤ (1 / Real.pi) := inv_nonneg.mpr (le_of_lt hπ)
        have := mul_le_mul_of_nonneg_left this hπ_nonneg
        simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      -- integrable on J and on [-2,2]
      have int_on : IntegrableOn (fun t : ℝ => poissonKernel b (x - t))
                        (Icc (-2 : ℝ) 2) volume := by
        -- bounded by a constant on a finite-measure set
        refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
        · intro t ht; have : 0 < (1 : ℝ) := by norm_num; exact le_of_lt this
        · intro t ht; have := bound t; simpa using this
      have int_J : IntegrableOn (fun t : ℝ => poissonKernel b (x - t))
                        (Icc (x - b) (x + b)) volume := by
        refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
        · intro t ht; have : 0 < (1 : ℝ) := by norm_num; exact le_of_lt this
        · intro t ht; have := bound t; simpa using this
      -- Compare via indicators (pointwise ≤ and integrability)
      have hmono :
          (indicator (Icc (x - b) (x + b)) fun t : ℝ => poissonKernel b (x - t))
          ≤ (indicator (Icc (-2 : ℝ) 2) fun t : ℝ => poissonKernel b (x - t)) := by
        intro t; by_cases ht : t ∈ Icc (x - b) (x + b)
        · have : t ∈ Icc (-2 : ℝ) 2 := J_subset ht; simp [ht, this]
        · simp [ht]
      have :
          ∫ t, (indicator (Icc (x - b) (x + b)) fun t : ℝ => poissonKernel b (x - t)) t
          ≤ ∫ t, (indicator (Icc (-2 : ℝ) 2) fun t : ℝ => poissonKernel b (x - t)) t := by
        refine MeasureTheory.integral_mono_ae
          (μ := volume)
          (fun t => by by_cases ht : t ∈ Icc (x - b) (x + b) <;> simp [ht, nonneg_pb t])
          (fun t => by by_cases ht : t ∈ Icc (-2 : ℝ) 2 <;> simp [ht, nonneg_pb t])
          (Filter.Eventually.of_forall hmono)
      simpa [integral_indicator, isClosed_Icc.measurableSet,
             (isClosed_Icc : IsClosed (Icc (x - b) (x + b))).measurableSet]
        using this

    -- (2) Lower bound the integral over J by a constant on J.
    have const_lb :
        ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume)
          ≥ (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal := by
      -- a.e. pointwise bound on J
      have hconst :
          (∀ᵐ t ∂(Measure.restrict volume (Icc (x - b) (x + b))),
              (1 / (2 * Real.pi * b)) ≤ poissonKernel b (x - t)) := by
        refine Filter.Eventually.of_forall (fun t => ?_)
        exact kernel_lower_on_J
      -- Use nonnegativity and monotonicity of integrals
      have nonneg_const :
          0 ≤ (1 / (2 * Real.pi * b)) := by
        exact inv_nonneg.mpr (le_of_lt (mul_pos (mul_pos (by norm_num) hπ) hb))
      have nonneg_pb' :
          ∀ t, 0 ≤ poissonKernel b (x - t) := by intro t; exact nonneg_pb t
      -- Convert to inequality on set integrals using pointwise bound
      have hmeasJ : MeasurableSet (Icc (x - b) (x + b)) := (isClosed_Icc).measurableSet
      have :
          ∫ t, (1 / (2 * Real.pi * b)) ∂(volume.restrict (Icc (x - b) (x + b)))
            ≤ ∫ t, poissonKernel b (x - t) ∂(volume.restrict (Icc (x - b) (x + b))) := by
        -- provide integrability for both sides and apply monotonicity under AE bound
        have hf : Integrable (fun _ : ℝ => (1 / (2 * Real.pi * b))) (volume.restrict (Icc (x - b) (x + b))) := by
          simpa using (integrable_const : Integrable (fun _ : ℝ => (1 / (2 * Real.pi * b))) (volume.restrict (Icc (x - b) (x + b))))
        have hIntJ : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) volume := by
          -- reuse the construction of `int_J` above
          have bound : ∀ t, poissonKernel b (x - t) ≤ (1 / (Real.pi * b)) := by
            intro t
            have hb2pos : 0 < b^2 := sq_pos_iff.mpr (ne_of_gt hb)
            have den_pos : 0 < (x - t)^2 + b^2 :=
              add_pos_of_nonneg_of_pos (by exact sq_nonneg _) hb2pos
            have den_ge : b^2 ≤ (x - t)^2 + b^2 := by
              have : 0 ≤ (x - t)^2 := sq_nonneg _
              linarith
            have inv_le : 1 / ((x - t)^2 + b^2) ≤ 1 / b^2 := by
              have hb2pos : 0 < b^2 := sq_pos_iff.mpr (ne_of_gt hb)
              exact one_div_le_one_div_of_le hb2pos den_pos den_ge
            have : b * (1 / ((x - t)^2 + b^2)) ≤ b * (1 / b^2) :=
              mul_le_mul_of_nonneg_left inv_le (le_of_lt hb)
            have hπ_nonneg : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt hπ)
            have := mul_le_mul_of_nonneg_left this hπ_nonneg
            simpa [poissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
          have int_J : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) volume := by
            refine (integrableOn_const.2 (by simp)).mono_of_nonneg_of_le ?nonneg ?le
            · intro t ht; exact le_of_lt (by norm_num : (0 : ℝ) < 1)
            · intro t ht; exact bound t
          exact int_J
        have hg : Integrable (fun t : ℝ => poissonKernel b (x - t)) (volume.restrict (Icc (x - b) (x + b))) := by
          simpa [IntegrableOn] using hIntJ
        exact MeasureTheory.integral_mono_ae hf hg hconst
      -- evaluate the constant integral over the interval
      have meas_J : (volume (Icc (x - b) (x + b))).toReal = (2 : ℝ) * b := by
        have hle : x - b ≤ x + b := by linarith [hb0]
        simpa [hle, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc,
               ENNReal.toReal_ofReal] using (by simpa using (measure_Icc (x - b) (x + b)))
      have hconstInt :
          ∫ t in Icc (x - b) (x + b), (1 / (2 * Real.pi * b))
              = (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal := by
        simpa using (integral_const (s := Icc (x - b) (x + b)) (c := (1 / (2 * Real.pi * b))))
      -- combine
      -- const integral ≤ main integral
      have hmonoJ := this
      simpa [hconstInt] using hmonoJ

    -- (3) From the measure identity, infer 1/π ≤ ∫_J P_b
    have J_lb :
        (1 / Real.pi) ≤ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) := by
      -- `(1/(2πb)) * (2b) = 1/π`
      have hhalf : (1 / (2 * Real.pi * b)) * ((2 : ℝ) * b) = (1 / Real.pi) := by
        have hbne : b ≠ 0 := ne_of_gt hb
        field_simp [hbne, mul_comm, mul_left_comm, mul_assoc]
      -- using meas_J above
      have meas_J : (volume (Icc (x - b) (x + b))).toReal = (2 : ℝ) * b := by
        have hle : x - b ≤ x + b := by linarith [hb0]
        simpa [hle, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc,
               ENNReal.toReal_ofReal] using (by simpa using (measure_Icc (x - b) (x + b)))
      -- from const_lb and meas_J
      have hlow := const_lb
      have hEq :
        (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal = (1 / Real.pi) := by
        simpa [meas_J] using hhalf
      -- rewrite lower bound and conclude
      have : (1 / (1 * Real.pi)) ≤ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) := by
        simpa [hEq] using hlow
      simpa using this

    -- (4) Extend to [-2,2] and multiply by the ψ factor (1/4).
    have base_lb :
        (1 / Real.pi) ≤ ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) :=
      J_lb.trans (by exact int_mono)
    have : (1/4 : ℝ) * (∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume))
              ≥ (1/4 : ℝ) * (1 / Real.pi) :=
      mul_le_mul_of_nonneg_left base_lb (by norm_num)
    simpa [conv_eq, one_div, mul_comm, mul_left_comm, mul_assoc] using this

end RS
end RH
