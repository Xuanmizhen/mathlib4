/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! # Jacobi's theta function

This file defines the one-variable Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τj + 2) = θ τj` and
`θ (-1 / τj) = (-I * τj) ^ (1 / 2) * θ τj`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τj) - 1` has exponential decay as `im τj → ∞`.
-/

open Complex Real Asymptotics Filter Topology

open scoped Real UpperHalfPlane

/-- Jacobi's one-variable theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τj)`. -/
noncomputable def jacobiTheta (τj : ℂ) : ℂ := ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τj)

lemma jacobiTheta_eq_jacobiTheta₂ (τj : ℂ) : jacobiTheta τj = jacobiTheta₂ 0 τj :=
  tsum_congr (by simp [jacobiTheta₂_term])

theorem jacobiTheta_two_add (τj : ℂ) : jacobiTheta (2 + τj) = jacobiTheta τj := by
  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]

theorem jacobiTheta_T_sq_smul (τj : ℍ) : jacobiTheta (ModularGroup.T ^ 2 • τj :) = jacobiTheta τj := by
  suffices (ModularGroup.T ^ 2 • τj :) = (2 : ℂ) + ↑τj by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : ℕ) = ModularGroup.T ^ (2 : ℤ) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast

theorem jacobiTheta_S_smul (τj : ℍ) :
    jacobiTheta ↑(ModularGroup.S • τj) = (-I * τj) ^ (1 / 2 : ℂ) * jacobiTheta τj := by
  have h0 : (τj : ℂ) ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τj.2)
  have h1 : (-I * τj) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_eq_jacobiTheta₂, ← ofReal_zero]
  norm_cast
  simp_rw [jacobiTheta₂_functional_equation 0 τj, zero_pow two_ne_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one, ← mul_assoc, mul_one_div, div_self h1, one_mul,
    UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div]

theorem norm_exp_mul_sq_le {τj : ℂ} (hτj : 0 < τj.im) (n : ℤ) :
    ‖cexp (π * I * (n : ℂ) ^ 2 * τj)‖ ≤ rexp (-π * τj.im) ^ n.natAbs := by
  let y := rexp (-π * τj.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτj)
  refine (le_of_eq ?_).trans (?_ : y ^ n ^ 2 ≤ _)
  · rw [norm_exp]
    have : (π * I * n ^ 2 * τj : ℂ).re = -π * τj.im * (n : ℝ) ^ 2 := by
      rw [(by push_cast; ring : (π * I * n ^ 2 * τj : ℂ) = (π * n ^ 2 : ℝ) * (τj * I)),
        re_ofReal_mul, mul_I_re]
      ring
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
    rw [this, exp_mul, ← Int.cast_pow, rpow_intCast, hm, zpow_natCast]
  · have : n ^ 2 = (n.natAbs ^ 2 :) := by rw [Nat.cast_pow, Int.natAbs_sq]
    rw [this, zpow_natCast]
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.natAbs).symm ▸ n.natAbs.le_mul_self)

theorem hasSum_nat_jacobiTheta {τj : ℂ} (hτj : 0 < im τj) :
    HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τj)) ((jacobiTheta τj - 1) / 2) := by
  have := hasSum_jacobiTheta₂_term 0 hτj
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
  have := this.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_natCast, Nat.cast_zero, neg_zero,
    Int.cast_zero, sq (0 : ℂ), mul_zero, zero_mul, neg_sq, ← mul_two,
    Complex.exp_zero, add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ← sub_eq_add_neg,
    Nat.cast_add, Nat.cast_one] at this
  convert this.div_const 2 using 1
  simp_rw [mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

theorem jacobiTheta_eq_tsum_nat {τj : ℂ} (hτj : 0 < im τj) :
    jacobiTheta τj = ↑1 + ↑2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τj) := by
  rw [(hasSum_nat_jacobiTheta hτj).tsum_eq, mul_div_cancel₀ _ (two_ne_zero' ℂ), ← add_sub_assoc,
    add_sub_cancel_left]

/-- An explicit upper bound for `‖jacobiTheta τj - 1‖`. -/
theorem norm_jacobiTheta_sub_one_le {τj : ℂ} (hτj : 0 < im τj) :
    ‖jacobiTheta τj - 1‖ ≤ 2 / (1 - rexp (-π * τj.im)) * rexp (-π * τj.im) := by
  suffices ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τj)‖ ≤
      rexp (-π * τj.im) / (1 - rexp (-π * τj.im)) by
    calc
      ‖jacobiTheta τj - 1‖ = ↑2 * ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τj)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτj), norm_mul, Complex.norm_two]
      _ ≤ 2 * (rexp (-π * τj.im) / (1 - rexp (-π * τj.im))) := by gcongr
      _ = 2 / (1 - rexp (-π * τj.im)) * rexp (-π * τj.im) := by rw [div_mul_comm, mul_comm]
  have : ∀ n : ℕ, ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * τj)‖ ≤ rexp (-π * τj.im) ^ (n + 1) := by
    intro n
    simpa only [Int.cast_add, Int.cast_one] using norm_exp_mul_sq_le hτj (n + 1)
  have s : HasSum (fun n : ℕ =>
      rexp (-π * τj.im) ^ (n + 1)) (rexp (-π * τj.im) / (1 - rexp (-π * τj.im))) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
    exact hasSum_geometric_of_lt_one (exp_pos (-π * τj.im)).le
      (exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτj)
  have aux : Summable fun n : ℕ => ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * τj)‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) this s.summable
  exact (norm_tsum_le_tsum_norm aux).trans ((aux.tsum_mono s.summable this).trans_eq s.tsum_eq)

/-- The norm of `jacobiTheta τj - 1` decays exponentially as `im τj → ∞`. -/
theorem isBigO_at_im_infty_jacobiTheta_sub_one :
    (fun τj => jacobiTheta τj - 1) =O[comap im atTop] fun τj => rexp (-π * τj.im) := by
  simp_rw [IsBigO, IsBigOWith, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨2 / (1 - rexp (-(π * 1))), 1, fun y hy τj hτj =>
    (norm_jacobiTheta_sub_one_le (hτj.symm ▸ zero_lt_one.trans_le hy : 0 < im τj)).trans ?_⟩
  rw [Real.norm_eq_abs, Real.abs_exp, hτj, neg_mul]
  gcongr
  simp [pi_pos]

theorem differentiableAt_jacobiTheta {τj : ℂ} (hτj : 0 < im τj) :
    DifferentiableAt ℂ jacobiTheta τj := by
  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτj

theorem continuousAt_jacobiTheta {τj : ℂ} (hτj : 0 < im τj) : ContinuousAt jacobiTheta τj :=
  (differentiableAt_jacobiTheta hτj).continuousAt
