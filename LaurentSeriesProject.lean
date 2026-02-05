import LaurentSeriesProject.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Path
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.UnitInterval

import Mathlib

set_option linter.flexible false

open Real
open MeasureTheory
open Set

section Laurent_series

variable {z₀ : ℂ} {z : ℂ} {r : ℝ} {R₁ : ℝ} {R₂ : ℝ} {f : ℂ → ℂ}

def analytic_on_annulus (z₀ : ℂ) (R₁ : ℝ) (R₂ : ℝ) (f : ℂ → ℂ) : Prop :=
  sorry

lemma analytic_const_shift (h : analytic_on_annulus z₀ R₁ R₂ f) : analytic_on_annulus 0 R₁ R₂ g := by
  sorry

lemma analytic_implies_cont (h : analytic_on_annulus z₀ R₁ R₂ f) : ContinuousOn f {z : ℂ | R₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < R₂} := by
  sorry

noncomputable def Laurent_coefficients (k : ℤ) (z₀ : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(z₀, r), (z - z₀)^(-(k+1)) * (f z)


noncomputable def Laurent_Series (z₀ : ℂ) (z : ℂ) (f : ℂ → ℂ) (r : ℝ) : ℂ :=
  ∑' (i : ℕ), (fun i ↦ (Laurent_coefficients i z₀ r f) * (z - z₀)^(i)) i
  + ∑' (i : ℕ), (fun i ↦ (Laurent_coefficients (-(i+1)) z₀ r f) * (1 / (z - z₀)^(i+1))) i


/-
In the proof we want to look at, we will need a complicted path-integral.
For this we will now construct the path, first as a general function
from the unit-interval, and then show that it is continuous.
-/

noncomputable def int_path_fun (z : ℂ) (R₁ : ℝ) (R₂ : ℝ) : (unitInterval → ℂ) := by
  intro x
  by_cases hz : z.im = 0
  · let r₁ := (R₁ + ‖z‖) / 2
    let r₂ := (R₂ + ‖z‖) / 2
    by_cases h : (x : ℝ) ≤ 1/2
    · by_cases h2 : (x : ℝ) ≤ 1/4
      · exact (r₂ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (4 * x + 1 / 4))
      · exact (r₂ + (r₁ - r₂) * 4 * (x-1/4)) * Complex.exp ((1/2) * Real.pi * Complex.I)
    · by_cases h2 : (x : ℝ) ≤ 3/4
      · exact (r₁ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ( -4 * x + 1 / 4))
      · exact (r₁ + (r₂ - r₁) * 4 * (x-3/4))* Complex.exp ((1/2) * Real.pi * Complex.I)
  · let r₁ := (R₁ + ‖z‖) / 2
    let r₂ := (R₂ + ‖z‖) / 2
    by_cases h : (x : ℝ) ≤ 1/2
    · by_cases h2 : (x : ℝ) ≤ 1/4
      · exact (r₂ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * 4 * x)
      · exact r₂ + (r₁ - r₂) * 4 * (x-1/4)
    · by_cases h2 : (x : ℝ) ≤ 3/4
      · exact (r₁ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * 4 * x)
      · exact r₁ + (r₂ - r₁) * 4 * (x-3/4)


/-
The following lemma is a technical statement which we will need to show that
the given path `int_path_def` is continuous. It is just an essential topological
property of the unit interval.
-/

lemma frontier_calculation (a : unitInterval) (b : ℝ) (hb1 : 0 < b) :
    a ∈ frontier {(x: unitInterval) | (x : ℝ) ≤ b} → ((a : ℝ) = b) := by
  rw [IsClosed.frontier_eq ?_]
  · rw [interior_eq_nhds']
    simp only [Set.mem_diff, Set.mem_setOf_eq, and_imp]
    intro ha ha2
    by_contra
    have ha3 : (a: ℝ) < b := by exact Std.lt_of_le_of_ne ha this
    have ha4 : {(x: unitInterval) | (x : ℝ) ≤ b} ∈ nhds a :=  by
      refine mem_interior_iff_mem_nhds.mp ?_
      refine mem_interior.mpr ?_
      by_cases ha_nonneg : a = 0
      · rw [ha_nonneg]
        use {x | (x : ℝ) < b}
        constructor
        · simp only [Set.setOf_subset_setOf, Subtype.forall, Set.mem_Icc, and_imp]
          intro y hy1 hy2 hy3
          linarith
        · constructor
          · refine isOpen_lt ?_ ?_
            · fun_prop
            · fun_prop
          · simp only [Set.mem_setOf_eq, Set.Icc.coe_zero]
            exact RCLike.ofReal_pos.mp hb1
      · push_neg at ha_nonneg
        use {x | (a : ℝ)/2 < ↑x ∧ ↑x < ((a : ℝ) + b)/2}
        simp only [Set.setOf_subset_setOf, and_imp, Subtype.forall, Set.mem_Icc, Set.mem_setOf_eq,
          half_lt_self_iff, unitInterval.coe_pos]
        constructor
        · intro y hy1 hy2 hy3 hy4
          linarith
        · constructor
          · refine Metric.isOpen_iff.mpr ?_
            intro x hx
            simp only [Set.mem_setOf_eq] at hx
            obtain ⟨hx1, hx2⟩ := hx
            have ha4 : 0 ≤ (a : ℝ) := by
              exact unitInterval.nonneg a
            use min (((x : ℝ) - (a : ℝ)/2)/2) ((((a : ℝ) + b)/2 - (x : ℝ))/2)
            constructor
            · simp
              constructor
              · linarith
              · linarith
            · intro y hy
              simp only [Metric.mem_ball, lt_inf_iff] at hy
              simp only [Set.mem_setOf_eq]
              obtain ⟨hy1, hy2⟩ := hy
              constructor
              · rw [show dist y x = |↑y - ↑x| from rfl] at hy1
                rw [abs_sub_lt_iff] at hy1
                obtain ⟨hy3, hy4⟩ := hy1
                by_cases hxy : (x : ℝ) < (y : ℝ)
                · grw [hxy] at hx1
                  exact hx1
                · push_neg at hxy
                  linarith
              · rw [show dist y x = |↑y - ↑x| from rfl] at hy2
                rw [abs_sub_lt_iff] at hy2
                obtain ⟨hy3, hy4⟩ := hy2
                by_cases hxy : (x : ℝ) < (y : ℝ)
                · linarith
                · push_neg at hxy
                  linarith
          · constructor
            · exact unitInterval.pos_iff_ne_zero.mpr ha_nonneg
            · linarith
    contradiction
  · refine isClosed_le ?_ ?_
    · fun_prop
    · fun_prop

/-
Now we prove continuity. In particular we proof that the path is of type Path from
its start to its endpoint. We need to make a case distinction on `z.im = 0` because
the path changes depending on that (We need to do this so that the path does not
pass through `z`, because the integrant will have a singularity there).
-/

noncomputable def int_path_real (z : ℂ) (hz : z.im = 0) (R₁ : ℝ) (R₂ : ℝ) :
    Path (X := ℂ) (((R₂ + ‖z‖) / 2) * Complex.exp (2 * Real.pi * Complex.I * (1 / 4)))
    (((R₂ + ‖z‖) / 2) * Complex.exp (2 * Real.pi * Complex.I * (1 / 4))) where
  toFun := int_path_fun z R₁ R₂
  continuous_toFun := by
    unfold int_path_fun
    simp [hz]
    refine continuous_if ?_ ?_ ?_
    · intro a ha
      have ha_front := frontier_calculation a (1/2) (one_half_pos)
      simp only [one_div] at ha_front
      specialize ha_front ha
      rw [ha_front]
      norm_num
      simp
      left
      refine Complex.exp_eq_exp_iff_exists_int.mpr ?_
      use 2
      ring_nf
    · refine ContinuousOn.if ?_ ?_ ?_
      · intro a ha
        have h1 := frontier_calculation a (1/4) (by norm_num)
        obtain ⟨ha1, ha2⟩ := ha
        simp only [one_div] at h1
        specialize h1 ha2
        rw [h1]
        simp
        left
        refine Complex.exp_eq_exp_iff_exists_int.mpr ?_
        use 1
        ring_nf
      · fun_prop
      · fun_prop
    · refine ContinuousOn.if ?_ ?_ ?_
      · intro a ha
        have h1 := frontier_calculation a (3/4) (by norm_num)
        obtain ⟨ha1, ha2⟩ := ha
        specialize h1 ha2
        rw [h1]
        simp
        left
        refine Complex.exp_eq_exp_iff_exists_int.mpr ?_
        use -3
        ring_nf
      · fun_prop
      · fun_prop
  source' := by
    unfold int_path_fun
    simp [hz]
  target' := by
    unfold int_path_fun
    norm_num
    simp [hz]
    left
    refine Complex.exp_eq_exp_iff_exists_int.mpr ?_
    use 0
    norm_num
    ring


noncomputable def int_path_nonreal (z : ℂ) (hz : z.im ≠ 0) (R₁ : ℝ) (R₂ : ℝ) :
    Path (X := ℂ) ((R₂ + ‖z‖) / 2) ((R₂ + ‖z‖) / 2) where
  toFun := int_path_fun z R₁ R₂
  continuous_toFun := by
    unfold int_path_fun
    simp [hz]
    refine continuous_if ?_ ?_ ?_
    · refine fun a a_1 ↦ ?_
      have h1 := frontier_calculation a (1/2) (one_half_pos)
      simp only [one_div] at h1
      specialize h1 a_1
      rw [h1]
      norm_num
      simp
      rw [Complex.exp_neg (2 * ↑π * Complex.I * 4 * 2⁻¹)]
      have h_euler : Complex.exp (2 * ↑π * Complex.I * 4 * 2⁻¹) = 1 := by
        refine Complex.exp_eq_one_iff.mpr ?_
        use 2
        ring
      rw [h_euler]
      simp
    · refine ContinuousOn.if ?_ ?_ ?_
      · intro a ha
        have h1 := frontier_calculation a (1/4) (by norm_num)
        obtain ⟨ha1, ha2⟩ := ha
        simp only [one_div] at h1
        specialize h1 ha2
        rw [h1]
        simp
      · fun_prop
      · fun_prop
    · refine ContinuousOn.if ?_ ?_ ?_
      · intro a ha
        have h1 := frontier_calculation a (3/4) (by norm_num)
        obtain ⟨ha1, ha2⟩ := ha
        specialize h1 ha2
        rw [h1]
        simp
        nth_rw 1 [mul_right_eq_self₀]
        left
        refine Complex.exp_eq_one_iff.mpr ?_
        use -3
        ring
      · fun_prop
      · fun_prop
  source' := by
    unfold int_path_fun
    simp [hz]
  target' := by
    unfold int_path_fun
    norm_num
    simp [hz]



/-
Now we have defined a Path of integration but we still need an integrant.
We will work with `∫ᶜ` which is a general path-integral, but it integrates
over 1-forms, so we construct one in the following definition.
The integrand itself is just the standart one that appears in the Cauchy integral formula.
-/

noncomputable def Cauchy_Integrant (x : ℂ) (z : ℂ) (f : ℂ → ℂ) :
    ℂ →L[ℝ] ℂ := ((f x) / (x - z)) • (1 : ℂ →L[ℝ] ℂ)


/-
Here we put all of the above together to define the Integral we want to work with.
-/

noncomputable def Integral_Complete_Path (z : ℂ) (R₁ : ℝ) (R₂ : ℝ) (f : ℂ → ℂ) : ℂ := by
  by_cases hz : z.im = 0
  · exact (2 * ↑Real.pi * Complex.I)⁻¹ * (8 * π) *
      ∫ᶜ x in (int_path_real z hz R₁ R₂), Cauchy_Integrant x z f
  · push_neg at hz
    exact (2 * ↑Real.pi * Complex.I)⁻¹ * (8 * π) *
      ∫ᶜ x in (int_path_nonreal z hz R₁ R₂), Cauchy_Integrant x z f


/-
What we have defined above is a integral over a closed loop where the
integrant is a Cauchy kernel. In particular `Closed_Help_Integral`
is equal to `f z` because of Cauchy's integral formula.
The problem is this only exists for circle/rectangle paths in Mathlib.
We could solve that by showing the paths are homotopy equivalent,
but the fact that integrals over equivalent paths have the same
value is also not yet in mathlib. So we will just assume the following.
-/

lemma Application_Cauchy (z : ℂ) (R₁ : ℝ) (R₁_pos : 0 < R₁) (R₂ : ℝ) (g : ℂ → ℂ)
    (hz_lower : R₁ < ‖z‖) (hz_upper : ‖z‖ < R₂) (h_analytic : analytic_on_annulus 0 R₁ R₂ g) :
    g z = Integral_Complete_Path z R₁ R₂ g := by sorry


/-
The next step in our proof is to decompose our path integral into to circular paths.
We will start by constructing both paths again. The calculations are a bit
easier here since we dont have a piecewise definition.
-/

noncomputable def circle_path_fun (z : ℂ) (R : ℝ) : (unitInterval → ℂ) := by
  intro x
  exact ((R + ‖z‖) / 2) * Complex.exp (2 * Real.pi * Complex.I * x)


noncomputable def Integral_inner_path (z : ℂ) (R₁ : ℝ) (f : ℂ → ℂ) : ℂ :=
    (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ w in C(0, (R₁ + ‖z‖) / 2), (f w) / (w - z)

noncomputable def Integral_outer_path (z : ℂ) (R₂ : ℝ) (f : ℂ → ℂ) : ℂ :=
    (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ w in C(0, (R₂ + ‖z‖) / 2), (f w) / (w - z)


/-
The following lemma decomposes the integral into our two circle integrals.
-/

lemma Integral_decomposition (R₁_pos : 0 ≤ R₁) (hz_lower : R₁ < ‖z‖) (hz_upper : ‖z‖ < R₂) :
    Integral_Complete_Path z R₁ R₂ f =
    (Integral_inner_path z R₁ f) + (Integral_outer_path z R₂ f) := by
  by_cases hz : z.im = 0
  · unfold Integral_Complete_Path
    simp [hz]
    unfold Integral_inner_path
    unfold Integral_outer_path
    sorry
  · unfold Integral_Complete_Path
    simp [hz]
    unfold Integral_inner_path
    unfold Integral_outer_path
    rw [← mul_add (2 * ↑π * Complex.I)⁻¹ (∮ (w : ℂ) in C(0, (R₁ + ‖z‖) / 2), f w / (w - z))
        (∮ (w : ℂ) in C(0, (R₂ + ‖z‖) / 2), f w / (w - z))]
    simp
    unfold int_path_nonreal
    rw [curveIntegral_def']

    simp [curveIntegralFun]
    unfold Path.extend
    simp [unitInterval]

    rw [mul_assoc]
    have h_cond : Complex.I * ((↑π)⁻¹ * 2⁻¹) ≠ 0 := by simp
    rw [mul_right_inj' h_cond]
    clear h_cond


    --decompose in half
    let IntFun := fun t ↦ (Cauchy_Integrant (IccExtend Path.extend._proof_1
      (int_path_fun z R₁ R₂) t) z f)
      (derivWithin (IccExtend Path.extend._proof_1 (int_path_fun z R₁ R₂)) (Icc 0 1) t)

    --We will need continuity often to prove integrability
    have h_cont : Continuous IntFun := by sorry


    have hab : IntervalIntegrable (IntFun) volume 0 (1 / 2) := by
      exact h_cont.intervalIntegrable (μ := volume) 0 (1 / 2)
    have hbc : IntervalIntegrable (IntFun) volume (1 / 2) 1 := by
      exact h_cont.intervalIntegrable (μ := volume) (1 /2 ) 1
    have h_decomp := intervalIntegral.integral_add_adjacent_intervals (a := 0)
      (b := 1/2) (c := 1) (μ := volume) (f := IntFun) (hab) (hbc)
    rw [← h_decomp]
    clear hab
    clear hbc
    clear h_decomp

    --decompose first half
    have hab : IntervalIntegrable (IntFun) volume 0 (1 / 4) := by
      exact h_cont.intervalIntegrable (μ := volume) 0 (1 / 4)
    have hbc : IntervalIntegrable (IntFun) volume (1 / 4) (1 / 2) := by
      exact h_cont.intervalIntegrable (μ := volume) (1 / 4) (1 / 2)
    have h_decomp := intervalIntegral.integral_add_adjacent_intervals (a := 0)
      (b := 1 / 4) (c := 1 / 2) (μ := volume) (f := IntFun) (hab) (hbc)
    rw [← h_decomp]
    clear hab
    clear hbc
    clear h_decomp

    --decompose second half
    have hab : IntervalIntegrable (IntFun) volume (1 / 2) (3 / 4) := by
      exact h_cont.intervalIntegrable (μ := volume) (1 / 2) (3 / 4)
    have hbc : IntervalIntegrable (IntFun) volume (3 / 4) 1 := by
      exact h_cont.intervalIntegrable (μ := volume) (3 / 4) 1
    have h_decomp := intervalIntegral.integral_add_adjacent_intervals (a := 1 / 2)
      (b := 3 / 4) (c := 1)  (μ := volume) (f := IntFun) (hab) (hbc)
    rw [← h_decomp]
    clear hab
    clear hbc
    clear h_decomp

    nth_rewrite 1 [add_assoc]
    nth_rewrite 3 [add_comm]
    nth_rewrite 2 [← add_assoc]

    --remove the lines that go in opposite directions
    have h_cancel : ((∫ (x : ℝ) in 1 / 4..1 / 2, IntFun x)
        + ∫ (x : ℝ) in 3 / 4..1, IntFun x) = 0 := by
      rw [add_eq_zero_iff_neg_eq]
      have hc : (-1 : ℝ) ≠ 0 := by norm_num
      have h_Int_rw := intervalIntegral.integral_comp_mul_left
          (c := -1) (IntFun) hc (a := - 1 / 4) (b := - 1 / 2)
      have h_rw : -1 * (-1 / 4 : ℝ) = 1 / 4 := by norm_num
      rw [h_rw] at h_Int_rw
      clear h_rw
      have h_rw : -1 * (-1 / 2 : ℝ) = 1 / 2 := by norm_num
      rw [h_rw] at h_Int_rw
      clear h_rw
      rw [inv_neg_one] at h_Int_rw
      rw [neg_one_smul] at h_Int_rw
      rw [← h_Int_rw]
      clear h_Int_rw
      have h_IntFun_rw : ∫ (x : ℝ) in -1 / 4..-1 / 2, IntFun (-1 * x)
          = ∫ (x : ℝ) in -1 / 4..-1 / 2, IntFun (-1 * (x + (5 / 4)) + (5 / 4)) := by
        congr
        simp
      rw [h_IntFun_rw]
      clear h_IntFun_rw
      have hc : (-1 : ℝ) ≠ 0 := by norm_num
      rw [intervalIntegral.integral_comp_add_right (fun t ↦ IntFun (-1 * t + (5 / 4))) (5 / 4)]
      have h_rw : (-1 / 4 : ℝ) + 5 / 4 = 1 := by norm_num
      rw [h_rw]
      clear h_rw
      have h_rw : (-1 / 2 : ℝ) + 5 / 4 = 3/ 4 := by norm_num
      rw [h_rw]
      clear h_rw
      rw [intervalIntegral.integral_symm (3 / 4) 1]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      unfold EqOn
      intro x hx
      have h_uIcc : uIcc (3 / 4 : ℝ) 1 = Icc (3 / 4 : ℝ) 1 := by
        refine uIcc_of_le ?_
        norm_num
      rw [h_uIcc] at hx
      clear h_uIcc
      rw [show (x ∈ Icc (3 / 4) 1) = (3 / 4 ≤ x ∧ x ≤ 1) from rfl] at hx
      obtain ⟨hx1, hx2⟩ := hx
      simp
      unfold IntFun
      have h_path_rw : (IccExtend Path.extend._proof_1 (int_path_fun z R₁ R₂) (-x + 5 / 4))
          = (IccExtend Path.extend._proof_1 (int_path_fun z R₁ R₂) x) := by
        unfold IccExtend
        simp
        unfold int_path_fun
        simp [hz]
        have h_cond : (projIcc 0 1 Path.extend._proof_1 (-x + 5 / 4) : ℝ) ≤ 2⁻¹ := by
          rw [show ↑(projIcc 0 1 Path.extend._proof_1 (-x + 5 / 4)) = max 0 (min 1 (-x + 5 / 4))
              from rfl]
          simp
          right
          norm_num at hx1
          grw [← hx1]
          norm_num
        simp [h_cond]
        clear h_cond
        have h_cond : ¬ (projIcc 0 1 Path.extend._proof_1 x : ℝ) ≤ 2⁻¹ := by
          rw [not_le]
          rw [show ↑(projIcc 0 1 Path.extend._proof_1 x) = max 0 (min 1 x) from rfl]
          simp
          right
          constructor
          · norm_num
          · linarith
        simp [h_cond]
        clear h_cond
        by_cases hx_boundry : x = (3 / 4) ∨ x = 1
        · obtain hx1 | hx2 := hx_boundry
          · rw [hx1]
            norm_num
            rw [show ↑(projIcc 0 1 Path.extend._proof_1 (1 / 2))
                = max 0 (min 1 (1 / 2 : ℝ)) from rfl]
            have h_rw : max 0 (min 1 (1 / 2 : ℝ)) = 1 / 2 := by norm_num
            rw [h_rw]
            clear h_rw
            rw [show ↑(projIcc 0 1 Path.extend._proof_1 (3 / 4))
                = max 0 (min 1 (3 / 4 : ℝ)) from rfl]
            have h_rw : max 0 (min 1 (3 / 4 : ℝ)) = 3 / 4 := by norm_num
            rw [h_rw]
            clear h_rw
            have h_cond : ¬ (1 / 2 : ℝ) ≤ 1 / 4 := by norm_num
            simp only [h_cond]
            clear h_cond
            simp
            norm_num
            rw [mul_assoc]
            norm_num
            nth_rw 1 [left_eq_mul₀ ?_]
            · refine Complex.exp_eq_one_iff.mpr ?_
              use -3
              ring_nf
            · rw [div_ne_zero_iff]
              constructor
              · norm_cast
                rw [← ne_eq]
                linarith
              · exact Ne.symm (NeZero.ne' 2)
          · rw [hx2]
            norm_num
            rw [show ↑(projIcc 0 1 Path.extend._proof_1 (1 / 4))
                = max 0 (min 1 (1 / 4 : ℝ)) from rfl]
            have h_rw : max 0 (min 1 (1 / 4 : ℝ)) = 1 / 4 := by norm_num
            rw [h_rw]
            clear h_rw
            simp
        · have h_cond : ¬ (projIcc 0 1 Path.extend._proof_1 (-x + 5 / 4) : ℝ) ≤ 4⁻¹ := by
            simp
            rw [show ↑(projIcc 0 1 Path.extend._proof_1 (-x + 5 / 4))
                = max 0 (min 1 (-x + 5 / 4)) from rfl]
            have hx3 : x < 1 := by
              push_neg at hx_boundry
              obtain ⟨hxb1, hxb2⟩ := hx_boundry
              exact Std.lt_of_le_of_ne hx2 hxb2
            simp
            right
            constructor
            · norm_num
            · rw [← lt_sub_iff_add_lt]
              norm_num
              exact hx3
          simp [h_cond]
          clear h_cond
          have h_cond : ¬ (projIcc 0 1 Path.extend._proof_1 x : ℝ) ≤ 3 / 4 := by
            simp
            rw [show ↑(projIcc 0 1 Path.extend._proof_1 x) = max 0 (min 1 x) from rfl]
            have hx3 : 3 / 4 < x := by
              push_neg at hx_boundry
              obtain ⟨hxb1, hxb2⟩ := hx_boundry
              exact Std.lt_of_le_of_ne hx1 (id (Ne.symm hxb1))
            simp
            right
            constructor
            · norm_num
            · exact hx3
          simp [h_cond]
          clear h_cond
          rw [show ↑(projIcc 0 1 Path.extend._proof_1 (-x + 5 / 4))
              = max 0 (min 1 (-x + 5 / 4)) from rfl]
          rw [show ↑(projIcc 0 1 Path.extend._proof_1 x) = max 0 (min 1 x) from rfl]
          have h_min_rw : (max 0 (min 1 (-x + 5 / 4))) = -x + 5 / 4 := by
            rw [max_eq_iff]
            right
            constructor
            · simp
              rw [← sub_le_iff_le_add]
              linarith
            · simp
              linarith
          rw [h_min_rw]
          clear h_min_rw
          have h_min_rw : (max 0 (min 1 x)) = x := by
            rw [max_eq_iff]
            right
            constructor
            · simp
              linarith
            · simp
              linarith
          rw [h_min_rw]
          clear h_min_rw
          simp
          ring_nf
      rw [h_path_rw]
      have h_path_deriv_rw : (derivWithin (IccExtend Path.extend._proof_1
          (int_path_fun z R₁ R₂)) (Icc 0 1) (-x + 5 / 4)) = -(derivWithin
          (IccExtend Path.extend._proof_1 (int_path_fun z R₁ R₂)) (Icc 0 1) x) := by
        rw [← derivWithin.neg]
        sorry
      rw [h_path_deriv_rw]
      clear h_path_rw
      clear h_path_deriv_rw
      simp

    rw [h_cancel]
    clear h_cancel
    rw [zero_add (∫ (x : ℝ) in 1 / 2..3 / 4, IntFun x)]
    rw [add_comm]


    -- equalize integrals
    have h_rescale := intervalIntegral.integral_comp_mul_add (a := 0) (b := 2 * π)
      (c := 1 / (8 * π)) (IntFun) (by norm_num) (1 / 2)
    have h_cond : (1 / (8 * π))⁻¹ ≠ 0 := by simp
    rw [← inv_smul_eq_iff₀ h_cond] at h_rescale
    clear h_cond
    have h_rw : 1 / (8 * π) * 0 + 1 / 2 = 1 / 2 := by norm_num
    rw [h_rw] at h_rescale
    clear h_rw
    have h_rw : 1 / (8 * π) * (2 * π) + 1 / 2 = 3 / 4 := by
      norm_num
      ring_nf
      rw [mul_inv_cancel₀ ?_]
      · norm_num
      · exact pi_ne_zero
    rw [h_rw] at h_rescale
    clear h_rw
    rw [← h_rescale]
    clear h_rescale

    have h_rescale := intervalIntegral.integral_comp_mul_add (a := 0) (b := 2 * π)
      (c := 1 / (8 * π)) (IntFun) (by norm_num) (0)
    have h_cond : (1 / (8 * π))⁻¹ ≠ 0 := by simp
    rw [← inv_smul_eq_iff₀ h_cond] at h_rescale
    clear h_cond
    have h_rw : 1 / (8 * π) * 0 + 0 = 0 := by norm_num
    rw [h_rw] at h_rescale
    clear h_rw
    have h_rw : 1 / (8 * π) * (2 * π) + 0 = 1 / 4 := by
      norm_num
      ring_nf
      rw [mul_inv_cancel₀ ?_]
      · norm_num
      · exact pi_ne_zero
    rw [h_rw] at h_rescale
    clear h_rw
    rw [← h_rescale]
    clear h_rescale

    rw [mul_add]
    rw [Complex.real_smul]
    rw [Complex.real_smul]
    rw [←mul_assoc ]
    have h_rw : 8 * (π : ℂ) * ↑(1 / (8 * π))⁻¹⁻¹ = 1 := by
      simp
      ring_nf
      rw [mul_inv_cancel₀ ?_]
      simp
    rw [h_rw]
    rw [←mul_assoc ]
    rw [h_rw]
    clear h_rw
    rw [one_mul]
    rw [one_mul]
    have h_int_eq1 : (∫ (x : ℝ) in 0..2 * π, IntFun (1 / (8 * π) * x + 1 / 2))
        = (∮ (w : ℂ) in C(0, (R₁ + ‖z‖) / 2), f w / (w - z)) := by
      unfold circleIntegral
      refine Eq.symm (intervalIntegral.integral_congr_ae_restrict ?_)

      have h_interval_rw : uIoc 0 (2 * π) = Ioc 0 (2 * π) := by
        unfold uIoc
        have h_rw : 0 ≤ 2 * π := by
          simp
          exact pi_nonneg
        simp [h_rw]
      rw [h_interval_rw]
      clear h_interval_rw

      have h_full_measure_Set : {x | 0 < x ∧ x < 2* π} ∈ ae (volume.restrict (Ioc 0 (2 * π))) := by
        refine mem_ae_iff.mpr ?_
        rw [compl_setOf fun a ↦ 0 < a ∧ a < 2 * π]
        simp
        have h_set_calc : ({a | 0 < a → 2 * π ≤ a} ∩ Ioc 0 (2 * π)) = {2 * π} := by
          ext x
          simp
          constructor
          · intro ⟨h1, h2⟩
            obtain ⟨hx_lower, hx_upper⟩ := h2
            specialize h1 hx_lower
            linarith
          · intro hx
            rw [hx]
            simp
            exact pi_pos
        simp [h_set_calc]

      have h_EqOn_Set : EqOn (fun θ ↦ deriv (circleMap 0 ((R₁ + ‖z‖) / 2)) θ •
          (fun w ↦ f w / (w - z)) (circleMap 0 ((R₁ + ‖z‖) / 2) θ))
          (fun x ↦ IntFun (1 / (8 * π) * x + 1 / 2)) {x | 0 < x ∧ x < 2* π} := by
        unfold EqOn
        intro x hx
        simp
        simp at hx
        obtain ⟨hx_lower, hx_upper⟩ := hx
        unfold IntFun
        unfold Cauchy_Integrant
        rw [ContinuousLinearMap.smul_apply]
        simp

        have h_derivs_agree : derivWithin (IccExtend Path.extend._proof_1 (int_path_fun z R₁ R₂))
            (Icc 0 1) (π⁻¹ * 8⁻¹ * x + 2⁻¹) = circleMap 0 ((R₁ + ‖z‖) / 2) x * Complex.I := by
          unfold int_path_fun
          simp [hz]
          sorry

        rw [h_derivs_agree]
        clear h_derivs_agree

        have h_fun_agree : f (IccExtend Path.extend._proof_1 (int_path_fun z R₁ R₂)
            (π⁻¹ * 8⁻¹ * x + 2⁻¹)) / (IccExtend Path.extend._proof_1
            (int_path_fun z R₁ R₂) (π⁻¹ * 8⁻¹ * x + 2⁻¹) - z)
            = f (circleMap 0 ((R₁ + ‖z‖) / 2) x) / (circleMap 0 ((R₁ + ‖z‖) / 2) x - z) := by
          sorry

        rw [h_fun_agree]
        clear h_fun_agree
        rw [mul_comm]


      have h_filter_rw := Filter.eventuallyEq_of_mem (l := ae (volume.restrict (Ioc 0 (2 * π))))
          (s := {x | 0 < x ∧ x < 2* π}) (h_full_measure_Set) (h_EqOn_Set)
      assumption
    have h_int_eq2 : ∫ (x : ℝ) in 0..2 * π, IntFun (1 / (8 * π) * x + 0)
        = ∮ (w : ℂ) in C(0, (R₂ + ‖z‖) / 2), f w / (w - z) := by
      sorry
    simp only [h_int_eq1]
    simp only [h_int_eq2]


/-
Our next big step is to decompose the cirlce integrals into sums,
but for this we need a bit of preperation
The main tool for decomposing the integrals into
sums will be this following geometric series.
-/

lemma Geometric_series (w : ℂ) (v : ℂ) (hw1 : 0 < ‖w‖) (hw2 : ‖v‖ < ‖w‖) :
    1 / (w - v) = (1/w) * (∑' (i : ℕ), (fun i ↦ (v/w)^i) i):= by
  have Step_1 : 1 / (w - v) = (1/w) * (1 / (1 - v/w)) := by
    rw [one_div_mul_one_div w (1 - v / w)]
    rw [mul_one_sub w (v / w)]
    rw [mul_div_cancel₀ v ?_]
    exact norm_pos_iff.mp hw1
  rw [Step_1]
  nth_rw 1 [mul_right_inj' ?_]
  · rw [tsum_geometric_of_norm_lt_one ?_]
    · simp
    · simp
      rw [@div_lt_one_iff]
      left
      constructor
      · assumption
      · assumption
  · refine one_div_ne_zero ?_
    exact norm_pos_iff.mp hw1


/-
Another big part we need to worry about is convergence of the sums.
For this we need an upper estimate for `f`.
-/

noncomputable def Upper_const (f : ℂ → ℂ) (R : ℝ) : ℝ :=
    sSup {a : ℝ | ∃ θ : ℝ, a = ‖f (circleMap 0 R θ)‖}

/-
This will be used as an upper estimate for `f`, so we first prove a few statements about it:
-/

lemma Sup_set_bounded (R : ℝ) (hf_cont : ContinuousOn
    f {s : ℂ | ∃ θ : ℝ, s = R * Complex.exp (↑θ * Complex.I)}) :
    BddAbove {a | ∃ θ, a = ‖f (circleMap 0 R θ)‖} := by
  refine (IsCompact.bddAbove ?_)
  have h_def_rw : {a | ∃ θ, a = ‖f (circleMap 0 R θ)‖}
      = (fun θ ↦ ‖f (circleMap 0 R θ)‖)'' Icc 0 (2 * π) := by
    rw [show (fun θ ↦ ‖f (circleMap 0 R θ)‖) '' Icc 0 (2 * π) =
            {x | ∃ a ∈ Icc 0 (2 * π), (
            fun θ ↦ ‖f (circleMap 0 R θ)‖) a = x} from rfl]
    ext x
    simp
    constructor
    · intro h
      obtain ⟨y, hy⟩ := h
      use y - 2 * π * ⌊(y / (2*π) )⌋
      constructor
      · constructor
        · simp
          rw [← le_div_iff₀' ?_]
          · exact Int.floor_le (y / (2 * π))
          · simp
            exact pi_pos
        · simp
          rw [← mul_one_add (2 * π) ↑⌊y / (2 * π)⌋]
          rw [← div_le_iff₀' ?_]
          · rw [add_comm]
            have h_floor := Int.floor_lt (z := ⌊y / (2 * π)⌋ + 1) (a := y / (2 * π))
            have h_ineq : ⌊y / (2 * π)⌋ < ⌊y / (2 * π)⌋ + 1 := by linarith
            obtain ⟨h_floor1, h_floor2⟩ := h_floor
            specialize h_floor1 h_ineq
            push_cast at h_floor1
            linarith
          · simp
            exact pi_pos
      · rw [hy]
        unfold circleMap
        have h_exp : Complex.exp (↑(y - 2 * π * ↑⌊y / (2 * π)⌋) * Complex.I)
            = Complex.exp (↑y * Complex.I) := by
          refine Complex.exp_eq_exp_iff_exists_int.mpr ?_
          use -⌊y / (2 * π)⌋
          rw [Complex.ofReal_sub y (2 * π * ↑⌊y / (2 * π)⌋)]
          rw [sub_mul (↑y) (↑(2 * π * ↑⌊y / (2 * π)⌋)) Complex.I]
          rw [← sub_eq_iff_eq_add']
          rw [sub_sub_cancel_left (↑y * Complex.I) (↑(2 * π * ↑⌊y / (2 * π)⌋) * Complex.I)]
          push_cast
          ring_nf
        rw [h_exp]
    · intro h
      obtain ⟨a, ha1, ha2⟩ := h
      use a
      rw [ha2]
  rw [h_def_rw]
  clear h_def_rw
  refine IsCompact.image (f := fun (θ: ℝ) ↦ ‖f (circleMap 0 R θ)‖) ?_ ?_
  · exact isCompact_Icc
  · unfold circleMap
    refine Continuous.norm ?_
    rw [← continuousOn_univ]
    have h_cont_inside : ContinuousOn (fun (θ : ℝ) ↦
        (circleMap 0 R θ)) univ := by
      fun_prop
    have h_domains : MapsTo (fun (θ : ℝ) ↦ (circleMap 0 R θ))
        univ {s | ∃ (θ : ℝ), s = R
        * Complex.exp (↑θ * Complex.I)} := by
      simp
      intro x
      use x
      unfold circleMap
      simp
    exact ContinuousOn.comp (g:= f) (f := fun (θ : ℝ) ↦
        (circleMap 0 R θ)) hf_cont h_cont_inside h_domains

lemma Sup_upper_bound (f : ℂ → ℂ) (R : ℝ) (hf_cont : ContinuousOn
    f {s : ℂ | ∃ θ : ℝ, s = R * Complex.exp (↑θ * Complex.I)}) (θ : ℝ)
    : ‖f (circleMap 0 R θ)‖ ≤ Upper_const f R := by
  refine (Real.le_sSup_iff ?_ ?_).mpr ?_
  · exact Sup_set_bounded R hf_cont
  · refine nonempty_def.mpr ?_
    use ‖f (circleMap 0 R 0)‖
    simp
    use 0
  · intro ε hε
    use ‖f (circleMap 0 R θ)‖
    simp
    constructor
    · use θ
    · assumption

lemma Sup_nonzero (f : ℂ → ℂ) (R : ℝ) (hf_cont : ContinuousOn
    f {s : ℂ | ∃ θ : ℝ, s = R * Complex.exp (↑θ * Complex.I)}) (hf_nonzero : ∃ θ : ℝ,
    f (circleMap 0 R θ) ≠ 0) : 0 < Upper_const f R := by
  unfold Upper_const
  rw [lt_csSup_iff ?_ ?_]
  · obtain ⟨θ, hθ⟩ := hf_nonzero
    use ‖f (circleMap 0 R θ)‖
    constructor
    · simp
      use θ
    · exact norm_pos_iff.mpr hθ
  · exact Sup_set_bounded R hf_cont
  · refine nonempty_def.mpr ?_
    use ‖f (circleMap 0 R 0)‖
    simp
    use 0

lemma Sup_zero (f : ℂ → ℂ) (R : ℝ) (hf_zero : ¬  ∃ θ : ℝ, f (circleMap 0 R θ)≠ 0)
    : Upper_const f R = 0 := by
  unfold Upper_const
  simp at hf_zero
  have h_set_rw : {a | ∃ θ, a = ‖f (circleMap 0 R θ)‖} = {0} := by
    ext a
    constructor
    · intro ha
      simp
      simp at ha
      obtain ⟨θ, hθ⟩ := ha
      rw [hf_zero θ] at hθ
      rw [hθ]
      exact norm_zero
    · intro ha
      simp at ha
      rw [ha]
      simp
      use 0
      rw [hf_zero 0]
      exact Eq.symm norm_zero
  rw [h_set_rw]
  exact csSup_singleton 0


lemma Outer_integral_to_Sum (hR₂ : 0 < R₂) (hz : ‖z‖ < R₂)
    (hf_cont : ContinuousOn f {s : ℂ | ∃ θ : ℝ, s = (R₂ + ‖z‖) / 2 * Complex.exp (↑θ * Complex.I)})
    : (Integral_outer_path z R₂ f) = ∑' (i : ℕ), ((2 * ↑Real.pi * Complex.I)⁻¹
    * ∮ w in C(0, (R₂ + ‖z‖) / 2), (w)^(-((i : ℤ)+1)) * (f w)) * z^i := by
  unfold Integral_outer_path

  --Reorder terms for preperaration.
  have h_assoc_rw : ∑' (i : ℕ), ((2 * ↑Real.pi * Complex.I)⁻¹
      * ∮ w in C(0, (R₂ + ‖z‖) / 2), (w)^(-((i : ℤ)+1)) * (f w)) * z^i
      = ∑' (i : ℕ), (2 * ↑π * Complex.I)⁻¹
      * ((∮ (w : ℂ) in C(0, (R₂ + ‖z‖) / 2), w ^ (-((i : ℤ) + 1)) * f w) * z ^ i) := by
    refine tsum_congr ?_
    intro i
    rw [mul_assoc]
  rw [h_assoc_rw]
  clear h_assoc_rw

  --Move out constant and remove it
  have Summable_condition : Summable (fun (i : ℕ) ↦ (∮ w in C(0, (R₂ + ‖z‖) / 2), w^(-((i : ℤ)+1))
      * (f w)) * z^i) := by

    have h_bound (i : ℕ) : ‖(∮ w in C(0, (R₂ + ‖z‖) / 2), w^(-((i : ℤ)+1)) * (f w)) * z^i‖
        ≤ (2 * π * (Upper_const f ((R₂ + ‖z‖) / 2))) * (‖z‖ / ((R₂ + ‖z‖) / 2))^i := by
      unfold circleIntegral
      rw [Complex.norm_mul]
      rw [div_pow ‖z‖ ((R₂ + ‖z‖) / 2) i]
      rw [show ‖z‖ ^ i / ((R₂ + ‖z‖) / 2) ^ i = ‖z‖ ^ i * (((R₂ + ‖z‖) / 2) ^ i)⁻¹ from rfl]
      rw [← Complex.norm_pow z i]
      rw [mul_comm]


      have h_bound_inside : ‖∫ (θ : ℝ) in 0..2 * π, deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) θ
          • (fun w ↦ w ^ (-((i : ℤ) + 1)) * f w)
          (circleMap 0 ((R₂ + ‖z‖) / 2) θ)‖ ≤ (2 * π *
          (Upper_const f ((R₂ + ‖z‖) / 2))) * (((R₂ + ‖z‖) / 2) ^ i)⁻¹ := by

        have h_move_norm : ‖∫ (θ : ℝ) in 0..2 * π, deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) θ
            • (fun w ↦ w ^ (-((i : ℤ) + 1)) * f w) (circleMap 0 ((R₂ + ‖z‖) / 2) θ)‖
            ≤ ∫ (θ : ℝ) in 0..2 * π, ‖deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) θ
            • (fun w ↦ w ^ (-((i : ℤ) + 1)) * f w) (circleMap 0 ((R₂ + ‖z‖) / 2) θ)‖ := by
          refine intervalIntegral.norm_integral_le_integral_norm ?_
          simp
          exact pi_nonneg
        grw [h_move_norm]
        clear h_move_norm

        have h_integrant_rw :(fun θ ↦ ‖deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) θ
            • (fun w ↦ w ^ (-((i: ℤ) + 1)) * f w)
            (circleMap 0 ((R₂ + ‖z‖) / 2) θ)‖) ≤ᶠ[ae volume]
            (fun θ ↦ (Upper_const f ((R₂ + ‖z‖) / 2)) * (((R₂ + ‖z‖) / 2) ^ i)⁻¹) := by
          refine ae_of_all (μ := volume) ?_
          intro θ
          simp
          norm_cast at hf_cont
          grw [Sup_upper_bound f ((R₂ + ‖z‖) / 2) hf_cont θ]
          rw [← mul_assoc]
          rw [← zpow_one_add₀ ?_ (-1 + -↑i)]
          · by_cases hf_nonzero : ∃ θ : ℝ, f (circleMap 0 ((R₂ + ‖z‖) / 2) θ)≠ 0
            · rw [← le_div_iff₀ (Sup_nonzero f ((R₂ + ‖z‖) / 2) hf_cont hf_nonzero)]
              have hC_nonzero : Upper_const f ((R₂ + ‖z‖) / 2) ≠ 0 := by
                rw [ne_iff_gt_or_lt]
                left
                exact Sup_nonzero f ((R₂ + ‖z‖) / 2) hf_cont hf_nonzero
              rw [mul_div_cancel_left₀ (((R₂ + ‖z‖) / 2) ^ i)⁻¹ (hC_nonzero)]
              rw [Int.add_neg_cancel_left 1 (-↑i)]
              rw [zpow_neg |(R₂ + ‖z‖) / 2| ↑i]
              simp
              rw [abs_of_pos ?_]
              rw [div_pos_iff_of_pos_right (by norm_num)]
              refine Right.add_pos_of_pos_of_nonneg hR₂ ?_
              exact norm_nonneg z
            · rw [Sup_zero f ((R₂ + ‖z‖) / 2) hf_nonzero]
              simp
          · rw [abs_ne_zero]
            rw [div_ne_zero_iff]
            constructor
            · have h_rw : 0 < R₂ + ‖z‖ := by
                refine Right.add_pos_of_pos_of_nonneg hR₂ (norm_nonneg z)
              exact Ne.symm (ne_of_lt h_rw)
            · exact Ne.symm (NeZero.ne' 2)




        have hab : 0 ≤ 2 * π := by
          simp
          exact pi_nonneg

        have hf : IntervalIntegrable (fun θ ↦ ‖deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) θ
            • (fun w ↦ w ^ (-((i: ℤ) + 1)) * f w) (circleMap 0 ((R₂ + ‖z‖) / 2) θ)‖)
            volume 0 (2 * π) := by
          have h_cont : Continuous (fun θ ↦ ‖deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) θ
              • (fun w ↦ w ^ (-((i : ℤ) + 1)) * f w) (circleMap 0 ((R₂ + ‖z‖) / 2) θ)‖) := by
            refine Continuous.norm ?_
            refine Continuous.smul ?_ ?_
            · unfold circleMap
              simp
              refine Continuous.mul ?_ ?_
              · continuity
              · have h_deriv_rw : (deriv fun (x: ℝ) ↦ Complex.exp ((x : ℂ) * Complex.I))
                    = (fun (x: ℝ) ↦ Complex.I * Complex.exp ((x : ℂ) * Complex.I)) := by
                  ext x
                  refine HasDerivAt.deriv ?_
                  rw [mul_comm]
                  have h_inner : HasDerivAt (fun (x : ℝ) ↦ ↑x * Complex.I) Complex.I x := by
                    have h_help := (HasDerivAt.ofReal_comp (hasDerivAt_id x)).smul_const Complex.I
                    simp at h_help
                    exact HasDerivAt.congr_deriv h_help rfl
                  refine HasDerivAt.comp x ?_ h_inner
                  exact Complex.hasDerivAt_exp (↑x * Complex.I)
                rw [h_deriv_rw]
                fun_prop
            · unfold circleMap
              simp
              refine Continuous.mul ?_ ?_
              · rw [continuous_iff_continuousAt]
                intro x
                let g := (fun (θ : ℝ) ↦ ((↑R₂ + ↑‖z‖) / 2 * Complex.exp (↑θ * Complex.I)))

                have h_nonzero : g x ≠ 0 ∨ 0 ≤ (-1 + -(i : ℤ)) := by
                  left
                  unfold g
                  simp
                  rw [← ne_eq]
                  rw [← norm_pos_iff]
                  rw [Complex.norm_add_eq ?_]
                  · rw [Complex.norm_of_nonneg (by linarith)]
                    rw [Complex.norm_of_nonneg (norm_nonneg z)]
                    refine Right.add_pos_of_pos_of_nonneg (by linarith) (norm_nonneg z)
                  · rw [Complex.arg_ofReal_of_nonneg (by linarith)]
                    rw [Complex.arg_ofReal_of_nonneg (norm_nonneg z)]
                refine ContinuousAt.zpow₀ (f := g) ?_ (-1 + -(i : ℤ)) h_nonzero
                unfold g
                fun_prop
              · rw [← continuousOn_univ]

                let g : ℝ → ℂ := fun (θ : ℝ) ↦
                  (↑R₂ + ↑‖z‖) / 2 * Complex.exp (↑θ * Complex.I)

                have h_inner : ContinuousOn g univ := by
                  unfold g
                  fun_prop

                have h_set_eq : MapsTo g univ
                    {s | ∃ (θ : ℝ), s = (↑R₂ + ↑‖z‖) / 2 * Complex.exp (↑θ * Complex.I)} := by
                  simp
                  intro x
                  use x

                have h_comp := ContinuousOn.comp (g := f) (f := g) hf_cont h_inner h_set_eq
                unfold Function.comp at h_comp
                unfold g at h_comp
                exact h_comp

          exact h_cont.intervalIntegrable (μ := volume) 0 (2 * π)


        have hg : IntervalIntegrable (fun t ↦ (Upper_const f ((R₂ + ‖z‖) / 2))
            * (((R₂ + ‖z‖) / 2) ^ i)⁻¹) volume 0 (2 * π) := by
          exact IntervalIntegrable.symm intervalIntegral.intervalIntegrable_const

        have h_int_rw := intervalIntegral.integral_mono_ae hab hf hg h_integrant_rw
        grw [h_int_rw]
        clear h_integrant_rw
        clear hf
        clear hg
        clear hab
        clear h_int_rw

        simp
        ring_nf
        exact Std.IsPreorder.le_refl
          (Upper_const f (R₂ * (1 / 2) + ‖z‖ * (1 / 2)) * π *
          (R₂ * (1 / 2) + ‖z‖ * (1 / 2))⁻¹ ^ i * 2)
      grw [h_bound_inside]
      ring_nf
      exact Std.IsPreorder.le_refl
        (‖z ^ i‖ * π * Upper_const f (R₂ * (1 / 2) + ‖z‖ * (1 / 2)) *
        (R₂ * (1 / 2) + ‖z‖ * (1 / 2))⁻¹ ^ i * 2)


    have h_geom : Summable (fun (i: ℕ) ↦ (‖z‖ / ((R₂ + ‖z‖) / 2))^i) := by
      refine summable_geometric_of_lt_one ?_ ?_
      · rw [div_nonneg_iff]
        left
        constructor
        · exact norm_nonneg z
        · rw [div_nonneg_iff]
          left
          constructor
          · refine Left.add_nonneg ?_ ?_
            · linarith
            · exact norm_nonneg z
          · exact zero_le_two
      · rw [div_lt_one ?_]
        · rw [lt_div_iff₀ ?_]
          · rw [← sub_lt_iff_lt_add]
            rw [← mul_sub_one ‖z‖ 2]
            norm_num
            assumption
          · exact zero_lt_two
        · rw [div_pos_iff_of_pos_right ?_]
          · refine Right.add_pos_of_pos_of_nonneg hR₂ ?_
            exact norm_nonneg z
          · exact zero_lt_two

    have h_geom_const : Summable (fun (i: ℕ) ↦ (2 * π
      * (Upper_const f ((R₂ + ‖z‖) / 2))) * (‖z‖ / ((R₂ + ‖z‖) / 2))^i) := by
      refine Summable.const_smul (2 * π * (Upper_const f ((R₂ + ‖z‖) / 2))) h_geom

    exact Summable.of_norm_bounded h_geom_const h_bound

  have Mul_out_const := Summable.tsum_mul_left (ι := ℕ) (α := ℂ)
    (f := fun (i : ℕ) ↦ (∮ w in C(0, (R₂ + ‖z‖) / 2), (w)^(-((i : ℤ)+1)) * (f w)) * z^i)
    (2 * ↑Real.pi * Complex.I)⁻¹ (Summable_condition)
  push_cast at Mul_out_const
  rw [Mul_out_const]
  clear Mul_out_const
  clear Summable_condition
  nth_rw 1 [mul_right_inj' (by norm_num)]


--Transform circle Intagral into normal one
  unfold circleIntegral
  have h_direction_bounds : 0 ≤ 2 * π := by
    simp
    exact pi_nonneg
  rw [intervalIntegral.integral_of_le h_direction_bounds]
  simp only [intervalIntegral.integral_of_le h_direction_bounds]


  --Move the `z^i` term inside the integral

  have h_int_rw : ∑' (i : ℕ), (∫ (θ : ℝ) in Ioc 0 (2 * π), deriv (circleMap 0 ((R₂ + ‖z‖)/2)) θ
      • (circleMap 0 ((R₂ + ‖z‖)/2) θ ^ (-((i : ℤ) + 1))
      * f (circleMap 0 ((R₂ + ‖z‖)/2) θ))) * z ^ i = ∑' (i : ℕ), (∫ (θ : ℝ) in Ioc 0 (2 * π),
      deriv (circleMap 0 ((R₂ + ‖z‖)/2)) θ • (circleMap 0 ((R₂ + ‖z‖)/2) θ ^ (-((i : ℤ) + 1))
      * f (circleMap 0 ((R₂ + ‖z‖)/2) θ)) * z ^ i) := by
    refine tsum_congr ?_
    intro i
    rw [← integral_mul_const (z ^ i) fun a ↦ deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) a •
        (circleMap 0 ((R₂ + ‖z‖) / 2) a ^ (-((i : ℤ) + 1)) * f (circleMap 0 ((R₂ + ‖z‖) / 2) a))]
  rw [h_int_rw]
  clear h_int_rw

  --Interchange sum and Integral
  let f_fubini := (fun (i : ℕ) ↦ (fun (t : ℝ) ↦ (deriv (circleMap 0 ((R₂ + ‖z‖)/2)) t
      • (circleMap 0 ((R₂ + ‖z‖)/2) t^(-((i : ℤ) + 1)) * f (circleMap 0 ((R₂ + ‖z‖)/2) t)) * z^i)))
  have h_fub_cond1 : ∀ (i : ℕ), AEStronglyMeasurable (f_fubini i)
      (volume.restrict (Ioc 0 (2 * π))) := by
    intro i
    unfold f_fubini
    sorry

  have h_fub_cond2 : ∑' (i : ℕ), ∫⁻ (a : ℝ) in Ioc 0 (2 * π), ‖f_fubini i a‖ₑ ≠ ⊤ := by
    let S (i : ℕ) := ∫⁻ (a : ℝ) in Ioc 0 (2 * π), ‖f_fubini i a‖ₑ

    let S_NNReal (i : ℕ) : NNReal := ENNReal.toNNReal (∫⁻ (a : ℝ) in Ioc 0 (2 * π), ‖f_fubini i a‖ₑ)

    have h_summable_cond := ENNReal.tsum_coe_ne_top_iff_summable (β := ℕ) (f := S_NNReal)

    have h_cast_rw : ∑' (i : ℕ), ∫⁻ (a : ℝ) in Ioc 0 (2 * π),
        ‖f_fubini i a‖ₑ = ∑' (i : ℕ), ENNReal.ofNNReal (S_NNReal i) := by
      refine tsum_congr ?_
      intro b
      unfold S_NNReal
      refine Eq.symm (ENNReal.coe_toNNReal ?_)
      refine (integrable_toReal_iff ?_ ?_).mp ?_
      · fun_prop
      · refine (ae_restrict_iff' ?_).mpr ?_
        · simp
        · refine ae_of_all volume ?_
          intro a ha
          exact enorm_ne_top
      · refine Integrable.norm ?_
        rw [← integrableOn_univ]
        have h_rw : IntegrableOn (f_fubini b) univ (volume.restrict (Ioc 0 (2 * π)))
            = IntegrableOn (f_fubini b) (Ioc 0 (2 * π)) := by simp [IntegrableOn]
        rw [h_rw]
        clear h_rw
        rw [←integrableOn_Icc_iff_integrableOn_Ioc
            (f := f_fubini b) (a := 0) (b := 2 * π) (μ := volume)]
        refine ContinuousOn.integrableOn_compact ?_ ?_
        · exact isCompact_Icc
        · unfold f_fubini
          simp
          refine ContinuousOn.mul ?_ (by fun_prop)
          refine ContinuousOn.mul (by fun_prop) ?_
          refine ContinuousOn.mul ?_ ?_
          · unfold circleMap
            simp
            intro x hx
            refine ContinuousWithinAt.zpow₀ ?_ (m := -1 + -(b : ℤ)) ?_
            · refine ContinuousWithinAt.mul ?_ ?_
              · exact continuousWithinAt_const
              · refine ContinuousWithinAt.cexp ?_
                refine ContinuousWithinAt.mul (by fun_prop) ?_
                exact continuousWithinAt_const
            · left
              simp
              rw [← ne_eq]
              rw [← norm_pos_iff]
              rw [Complex.norm_add_eq ?_]
              · rw [Complex.norm_of_nonneg (by linarith)]
                rw [Complex.norm_of_nonneg (norm_nonneg z)]
                refine Right.add_pos_of_pos_of_nonneg (by linarith) (norm_nonneg z)
              · rw [Complex.arg_ofReal_of_nonneg (by linarith)]
                rw [Complex.arg_ofReal_of_nonneg (norm_nonneg z)]
          · unfold circleMap
            let g : ℝ → ℂ := fun (θ : ℝ) ↦
                (↑R₂ + ↑‖z‖) / 2 * Complex.exp (↑θ * Complex.I)

            have h_inner : ContinuousOn g univ := by
              unfold g
              fun_prop

            have h_set_eq : MapsTo g univ
                {s | ∃ (θ : ℝ), s = (↑R₂ + ↑‖z‖) / 2 * Complex.exp (↑θ * Complex.I)} := by
              simp
              intro x
              use x

            have h_comp := ContinuousOn.comp (g := f) (f := g) hf_cont h_inner h_set_eq
            unfold Function.comp at h_comp
            unfold g at h_comp
            simp
            exact ContinuousOn.mono h_comp fun ⦃a⦄ a_1 ↦ trivial
    rw [h_cast_rw]
    clear h_cast_rw

    apply h_summable_cond.2
    unfold S_NNReal
    sorry

  have h_fubini := integral_tsum (α := ℝ) (ι := ℕ) (μ := volume.restrict (Ioc 0 (2 * π)))
      (f := f_fubini) (h_fub_cond1) (h_fub_cond2)
  unfold f_fubini at h_fubini
  rw [← h_fubini]
  clear h_fub_cond1
  clear h_fub_cond2
  clear h_fubini
  clear f_fubini

  --move out derivative term
  simp only [smul_eq_mul]
  simp only [mul_assoc]
  simp only [tsum_mul_left]

  -- move the `z^x` inside the other exponent
  have h_comm_rw : ∫ (a : ℝ) in Ioc 0 (2 * π), deriv (circleMap 0 ((R₂ + ‖z‖)/2)) a
      * ∑' (x : ℕ), circleMap 0 ((R₂ + ‖z‖)/2) a ^ (-((x : ℤ) + 1))
      * (f (circleMap 0 ((R₂ + ‖z‖)/2) a) * z ^ x)
      = ∫ (a : ℝ) in Ioc 0 (2 * π), deriv (circleMap 0 ((R₂ + ‖z‖)/2)) a
      * f (circleMap 0 ((R₂ + ‖z‖)/2) a) * ((1 / circleMap 0 ((R₂ + ‖z‖)/2) a)
      * ∑' (x : ℕ), (z / circleMap 0 ((R₂ + ‖z‖)/2) a) ^ x) := by
    refine setIntegral_congr_fun ?_ ?_
    · simp
    · unfold EqOn
      intro x hx
      simp
      nth_rewrite 2 [mul_assoc]
      rw [mul_eq_mul_left_iff]
      left
      rw [← tsum_mul_left]
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro i
      ring_nf
      rw [mul_assoc]
      rw [mul_comm]
      nth_rewrite 2 [mul_assoc]
      simp
      left
      rw [zpow_sub₀ ?_ (-1) ↑i]
      · simp
        ring_nf
      · simp
        have hz_pos : 0 ≤ ‖z‖ :=  by exact norm_nonneg z
        linarith
  rw [h_comm_rw]
  clear h_comm_rw

  -- rewrite with the geometric series
  have h_geom_rw : ∫ (a : ℝ) in Ioc 0 (2 * π),  deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) a
      * f (circleMap 0 ((R₂ + ‖z‖) / 2) a) * (1 / circleMap 0 ((R₂ + ‖z‖) / 2) a
      * ∑' (x : ℕ), (z / circleMap 0 ((R₂ + ‖z‖) / 2) a) ^ x) =
      ∫ (a : ℝ) in Ioc 0 (2 * π), deriv (circleMap 0 ((R₂ + ‖z‖) / 2)) a
      * f (circleMap 0 ((R₂ + ‖z‖) / 2) a) * (1 / (circleMap 0 ((R₂ + ‖z‖) / 2) a - z)) := by
    refine setIntegral_congr_fun ?_ ?_
    · simp
    · unfold EqOn
      intro x hx
      simp
      left
      rw [inv_eq_one_div (circleMap 0 ((R₂ + ‖z‖) / 2) x)]
      rw [← Geometric_series (circleMap 0 ((R₂ + ‖z‖) / 2) x) (z)]
      · exact one_div (circleMap 0 ((R₂ + ‖z‖) / 2) x - z)
      · simp
        rw [← ne_eq (R₂ + ‖z‖) 0]
        rw [ne_iff_gt_or_lt]
        left
        have h_abs_pos : 0 ≤ ‖z‖ := by exact norm_nonneg z
        linarith
      · simp
        rw [abs_of_pos ?_]
        · rw [lt_div_iff₀ ?_]
          · linarith
          · simp
        · simp
          have h_abs_pos : 0 ≤ ‖z‖ := by exact norm_nonneg z
          linarith
  rw [h_geom_rw]
  clear h_geom_rw

  -- unfolding
  simp
  refine setIntegral_congr_fun ?_ ?_
  · simp
  · unfold EqOn
    intro x hx
    simp
    ring_nf



/- Here is the analogous version -/

lemma Inner_integral_to_Sum (hR₁ : 0 < R₁) (hz : R₁ < ‖z‖) : (Integral_inner_path z R₁ f) =
    ∑' (i : ℕ), ((2 * ↑Real.pi * Complex.I)⁻¹
    * ∮ w in C(0, (R₁ + ‖z‖) / 2), (w)^i * (f w)) * z^(- ((i : ℤ) + 1)) := by sorry

/-
For the laurent coeffictients we need a different radius to integrate over.
So we need to shift integrals again, which we will dentote with the following lemmas.
-/

lemma Circle_path_shift (R : ℝ ) (r : ℝ) (i : ℤ) (R₁ : ℝ) (R₁_pos : 0 < R₁) (R₂ : ℝ)
    (hR_lower : R₁ < R) (hR_upper : R < R₂) (hr_lower : R₁ < r) (hr_upper : r < R₂)
    (h_analytic : analytic_on_annulus z₀ R₁ R₂ f) :
    ∮ w in C(0, R), (w)^i * (f w) = ∮ w in C(0, r), (w)^i * (f w) := by sorry


theorem Laurent_theorem (R₁_pos : 0 < R₁) (hz_lower : R₁ < ‖z - z₀‖)
    (hz_upper : ‖z - z₀‖ < R₂) (h_analytic : analytic_on_annulus z₀ R₁ R₂ f)
    (hr_lower : R₁ < r) (hr_upper : r < R₂) : f z = Laurent_Series z₀ z f r := by
  let g : ℂ → ℂ := by
    intro z
    exact f (z + z₀)
  have h_fg_rw : f z = g (z - z₀) := by
    unfold g
    simp
  rw [h_fg_rw]
  have hg_analytic : analytic_on_annulus 0 R₁ R₂ g := by
    exact analytic_const_shift h_analytic
  rw [Application_Cauchy (z - z₀) R₁ R₁_pos R₂ g hz_lower hz_upper hg_analytic]
  rw [Integral_decomposition (by linarith) hz_lower hz_upper]
  unfold Laurent_Series
  rw [add_comm]
  congr
  · rw [Outer_integral_to_Sum]
    · refine tsum_congr ?_
      intro i
      unfold Laurent_coefficients
      simp
      left
      have hR_lower : R₁ < (R₂ + ‖z - z₀‖) / 2 := by linarith
      have hR_upper : (R₂ + ‖z - z₀‖) / 2 < R₂ := by linarith
      rw [Circle_path_shift ((R₂ + ‖z - z₀‖) / 2) r (-1 + (-i : ℤ)) R₁ R₁_pos
          R₂ hR_lower hR_upper hr_lower hr_upper h_analytic (f:= g) (z₀ := z₀)]
      unfold circleIntegral
      have h_interval : 0 ≤ 2 * π := by
        simp
        exact pi_nonneg
      rw [intervalIntegral.integral_of_le h_interval]
      rw [intervalIntegral.integral_of_le h_interval]
      refine setIntegral_congr_fun ?_ ?_
      · simp
      · unfold EqOn
        intro x hx
        simp
        left
        left
        unfold g
        unfold circleMap
        ring_nf
    · linarith
    · assumption
    · have h_cont := analytic_implies_cont hg_analytic
      refine continuousOn_of_forall_continuousAt ?_
      rw [IsOpen.continuousOn_iff ?_] at h_cont
      · intro x hx
        have hx_restrict : x ∈ {z | R₁ < ‖z - 0‖ ∧ ‖z - 0‖ < R₂} := by
          simp
          simp at hx
          obtain ⟨θ, hθ⟩ := hx
          rw [hθ]
          constructor
          · rw [Complex.norm_mul]
            rw [Complex.norm_exp_ofReal_mul_I θ]
            simp
            rw [lt_div_iff₀' zero_lt_two]
            rw [SameRay.norm_add ?_]
            · simp
              grw [hz_lower]
              rw [abs_of_pos (by linarith)]
              rw [← sub_lt_iff_lt_add]
              rw [← sub_one_mul 2 ‖z - z₀‖]
              norm_num
              exact hz_upper
            · refine Complex.sameRay_of_arg_eq ?_
              rw [Complex.arg_ofReal_of_nonneg (by linarith)]
              rw [Complex.arg_ofReal_of_nonneg (norm_nonneg (z - z₀))]
          · rw [norm_mul]
            rw [Complex.norm_exp_ofReal_mul_I θ]
            simp
            rw [div_lt_iff₀ zero_lt_two]
            rw [Complex.norm_add_eq ?_]
            · simp
              rw [abs_of_pos (by linarith)]
              rw [← lt_tsub_iff_left]
              rw [← mul_sub_one R₂ 2]
              norm_num
              exact hz_upper
            · rw [Complex.arg_ofReal_of_nonneg (by linarith)]
              rw [Complex.arg_ofReal_of_nonneg (norm_nonneg (z - z₀))]
        specialize h_cont hx_restrict
        assumption
      · simp
        rw [Metric.isOpen_iff]
        intro x hx
        use min ((‖x‖ - R₁)/2) ((R₂ - ‖x‖)/2)
        simp
        simp at hx
        obtain ⟨hx1, hx2⟩ := hx
        constructor
        · constructor
          · exact hx1
          · exact hx2
        · refine subset_setOf.mpr ?_
          intro y
          simp
          intro hy1 hy2
          constructor
          · rw [show dist y x = ‖y - x‖ from rfl] at hy1
            rw [lt_div_iff₀ zero_lt_two] at hy1
            rw [lt_sub_comm] at hy1
            by_cases hxy : x = y
            · rw [← hxy]
              exact hx1
            · push_neg at hxy
              grw [hy1]
              rw [sub_lt_comm]
              grw [norm_sub_norm_le]
              rw [norm_sub_rev x y]
              rw [lt_mul_iff_one_lt_right (norm_sub_pos_iff.mpr (id (Ne.symm hxy)))]
              exact one_lt_two
          · rw [show dist y x = ‖y - x‖ from rfl] at hy2
            rw [lt_div_iff₀ zero_lt_two] at hy2
            rw [lt_sub_iff_add_lt] at hy2
            by_cases hxy : x = y
            · rw [← hxy]
              exact hx2
            · push_neg at hxy
              grw [← hy2]
              rw [← sub_lt_iff_lt_add]
              grw [norm_sub_norm_le]
              rw [lt_mul_iff_one_lt_right (norm_sub_pos_iff.mpr (id (Ne.symm hxy)))]
              exact one_lt_two
  · rw [Inner_integral_to_Sum]
    · refine tsum_congr ?_
      intro i
      unfold Laurent_coefficients
      simp
      rw [mul_assoc]
      nth_rewrite 2 [mul_assoc]
      simp
      have h_cast_rw : ∮ (w : ℂ) in C(0, (R₁ + ‖z - z₀‖) / 2), w ^ i * g w
          = ∮ (w : ℂ) in C(0, (R₁ + ‖z - z₀‖) / 2), w ^ (i : ℤ) * g w := by simp
      rw [h_cast_rw]
      clear h_cast_rw
      have hR_lower : R₁ < (R₁ + ‖z - z₀‖) / 2 := by linarith
      have hR_upper : (R₁ + ‖z - z₀‖) / 2 < R₂ := by linarith
      rw [Circle_path_shift ((R₁ + ‖z - z₀‖) / 2) r (i : ℤ) R₁ R₁_pos
          R₂ hR_lower hR_upper hr_lower hr_upper h_analytic (f:= g) (z₀ := z₀)]
      unfold circleIntegral
      rw [←intervalIntegral.integral_mul_const ((z - z₀) ^ (-1 + (-i : ℤ))) fun x ↦
          deriv (circleMap 0 r) x • (fun w ↦ w ^ (i : ℤ) * g w) (circleMap 0 r x)]
      rw [← intervalIntegral.integral_mul_const ((z - z₀) ^ ((i: ℤ) + 1))⁻¹ fun x ↦
          deriv (circleMap z₀ r) x • (fun z ↦ (z - z₀) ^ i * f z) (circleMap z₀ r x)]
      have h_interval : 0 ≤ 2 * π := by
        simp
        exact pi_nonneg
      rw [intervalIntegral.integral_of_le h_interval]
      rw [intervalIntegral.integral_of_le h_interval]
      refine setIntegral_congr_fun ?_ ?_
      · simp
      · unfold EqOn
        intro x hx
        simp
        unfold g
        unfold circleMap
        rw [← zpow_neg (z - z₀) (↑i + 1)]
        simp
        left
        left
        left
        ring_nf
    · linarith
    · assumption

end Laurent_series
