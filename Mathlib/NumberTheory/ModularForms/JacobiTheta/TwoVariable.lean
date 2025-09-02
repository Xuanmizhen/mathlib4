/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The two-variable Jacobi theta function

This file defines the two-variable Jacobi theta function

$$\theta(z, \tau) = \sum_{n \in \mathbb{Z}} \exp (2 i \pi n z + i \pi n ^ 2 \tau),$$

and proves the functional equation relating the values at `(z, τj)` and `(z / τj, -1 / τj)`,
using Poisson's summation formula. We also show holomorphy (jointly in both variables).

Additionally, we show some analogous results about the derivative (in the `z`-variable)

$$\theta'(z, τj) = \sum_{n \in \mathbb{Z}} 2 \pi i n \exp (2 i \pi n z + i \pi n ^ 2 \tau).$$

(Note that the Mellin transform of `θ` will give us functional equations for `L`-functions
of even Dirichlet characters, and that of `θ'` will do the same for odd Dirichlet characters.)
-/

open Complex Real Asymptotics Filter Topology

open scoped ComplexConjugate

noncomputable section

section term_defs
/-!
## Definitions of the summands
-/

/-- Summand in the series for the Jacobi theta function. -/
def jacobiTheta₂_term (n : ℤ) (z τj : ℂ) : ℂ := cexp (2 * π * I * n * z + π * I * n ^ 2 * τj)

/-- Summand in the series for the Fréchet derivative of the Jacobi theta function. -/
def jacobiTheta₂_term_fderiv (n : ℤ) (z τj : ℂ) : ℂ × ℂ →L[ℂ] ℂ :=
  cexp (2 * π * I * n * z + π * I * n ^ 2 * τj) •
    ((2 * π * I * n) • (ContinuousLinearMap.fst ℂ ℂ ℂ) +
      (π * I * n ^ 2) • (ContinuousLinearMap.snd ℂ ℂ ℂ))

lemma hasFDerivAt_jacobiTheta₂_term (n : ℤ) (z τj : ℂ) :
    HasFDerivAt (fun p : ℂ × ℂ ↦ jacobiTheta₂_term n p.1 p.2)
    (jacobiTheta₂_term_fderiv n z τj) (z, τj) := by
  let f : ℂ × ℂ → ℂ := fun p ↦ 2 * π * I * n * p.1 + π * I * n ^ 2 * p.2
  suffices HasFDerivAt f ((2 * π * I * n) • (ContinuousLinearMap.fst ℂ ℂ ℂ)
    + (π * I * n ^ 2) • (ContinuousLinearMap.snd ℂ ℂ ℂ)) (z, τj) from this.cexp
  exact (hasFDerivAt_fst.const_mul _).add (hasFDerivAt_snd.const_mul _)

/-- Summand in the series for the `z`-derivative of the Jacobi theta function. -/
def jacobiTheta₂'_term (n : ℤ) (z τj : ℂ) := 2 * π * I * n * jacobiTheta₂_term n z τj

end term_defs

section term_bounds
/-!
## Bounds for the summands

We show that the sums of the three functions `jacobiTheta₂_term`, `jacobiTheta₂'_term` and
`jacobiTheta₂_term_fderiv` are locally uniformly convergent in the domain `0 < im τj`, and diverge
everywhere else.
-/

lemma norm_jacobiTheta₂_term (n : ℤ) (z τj : ℂ) :
    ‖jacobiTheta₂_term n z τj‖ = rexp (-π * n ^ 2 * τj.im - 2 * π * n * z.im) := by
  rw [jacobiTheta₂_term, Complex.norm_exp, (by push_cast; ring :
    (2 * π : ℂ) * I * n * z + π * I * n ^ 2 * τj = (π * (2 * n) :) * z * I + (π * n ^ 2 :) * τj * I),
    add_re, mul_I_re, im_ofReal_mul, mul_I_re, im_ofReal_mul]
  ring_nf

/-- A uniform upper bound for `jacobiTheta₂_term` on compact subsets. -/
lemma norm_jacobiTheta₂_term_le {S T : ℝ} (hT : 0 < T) {z τj : ℂ}
    (hz : |im z| ≤ S) (hτj : T ≤ im τj) (n : ℤ) :
    ‖jacobiTheta₂_term n z τj‖ ≤ rexp (-π * (T * n ^ 2 - 2 * S * |n|)) := by
  simp_rw [norm_jacobiTheta₂_term, Real.exp_le_exp, sub_eq_add_neg, neg_mul, ← neg_add,
    neg_le_neg_iff, mul_comm (2 : ℝ), mul_assoc π, ← mul_add, mul_le_mul_iff_right₀ pi_pos,
    mul_comm T, mul_comm S]
  refine add_le_add (mul_le_mul le_rfl hτj hT.le (sq_nonneg _)) ?_
  rw [← mul_neg, mul_assoc, mul_assoc, mul_le_mul_iff_right₀ two_pos, mul_comm, neg_mul, ← mul_neg]
  refine le_trans ?_ (neg_abs_le _)
  rw [mul_neg, neg_le_neg_iff, abs_mul, Int.cast_abs]
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

/-- A uniform upper bound for `jacobiTheta₂'_term` on compact subsets. -/
lemma norm_jacobiTheta₂'_term_le {S T : ℝ} (hT : 0 < T) {z τj : ℂ}
    (hz : |im z| ≤ S) (hτj : T ≤ im τj) (n : ℤ) :
    ‖jacobiTheta₂'_term n z τj‖ ≤ 2 * π * |n| * rexp (-π * (T * n ^ 2 - 2 * S * |n|)) := by
  rw [jacobiTheta₂'_term, norm_mul]
  refine mul_le_mul (le_of_eq ?_) (norm_jacobiTheta₂_term_le hT hz hτj n)
    (norm_nonneg _) (by positivity)
  simp only [norm_mul, Complex.norm_two, norm_I, Complex.norm_of_nonneg pi_pos.le,
    norm_intCast, mul_one, Int.cast_abs]

/-- The uniform bound we have given is summable, and remains so after multiplying by any fixed
power of `|n|` (we shall need this for `k = 0, 1, 2`). -/
lemma summable_pow_mul_jacobiTheta₂_term_bound (S : ℝ) {T : ℝ} (hT : 0 < T) (k : ℕ) :
    Summable (fun n : ℤ ↦ (|n| ^ k : ℝ) * Real.exp (-π * (T * n ^ 2 - 2 * S * |n|))) := by
  suffices Summable (fun n : ℕ ↦ (n ^ k : ℝ) * Real.exp (-π * (T * n ^ 2 - 2 * S * n))) by
    apply Summable.of_nat_of_neg <;>
    simpa only [Int.cast_neg, neg_sq, abs_neg, Int.cast_natCast, Nat.abs_cast]
  apply summable_of_isBigO_nat (summable_pow_mul_exp_neg_nat_mul k zero_lt_one)
  apply IsBigO.mul (isBigO_refl _ _)
  refine Real.isBigO_exp_comp_exp_comp.mpr (Tendsto.isBoundedUnder_le_atBot ?_)
  simp_rw [← tendsto_neg_atTop_iff, Pi.sub_apply]
  conv =>
    enter [1, n]
    rw [show -(-π * (T * n ^ 2 - 2 * S * n) - -1 * n) = n * (π * T * n - (2 * π * S + 1)) by ring]
  refine tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _ ?_)
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos pi_pos hT)

/-- The series defining the theta function is summable if and only if `0 < im τj`. -/
lemma summable_jacobiTheta₂_term_iff (z τj : ℂ) : Summable (jacobiTheta₂_term · z τj) ↔ 0 < im τj := by
  -- NB. This is a statement of no great mathematical interest; it is included largely to avoid
  -- having to impose `0 < im τj` as a hypothesis on many later lemmas.
  refine Iff.symm ⟨fun hτj ↦ ?_, fun h ↦ ?_⟩ -- do quicker implication first!
  · refine (summable_pow_mul_jacobiTheta₂_term_bound |im z| hτj 0).of_norm_bounded ?_
    simpa only [pow_zero, one_mul] using norm_jacobiTheta₂_term_le hτj le_rfl le_rfl
  · by_contra! hτj
    rcases lt_or_eq_of_le hτj with hτj | hτj
    · -- easy case `im τj < 0`
      suffices Tendsto (fun n : ℕ ↦ ‖jacobiTheta₂_term ↑n z τj‖) atTop atTop by
        replace h := (h.comp_injective (fun a b ↦ Int.ofNat_inj.mp)).tendsto_atTop_zero.norm
        exact atTop_neBot.ne (disjoint_self.mp <| h.disjoint (disjoint_nhds_atTop _) this)
      simp only [norm_jacobiTheta₂_term, Int.cast_natCast]
      conv =>
        enter [1, n]
        rw [show -π * n ^ 2 * τj.im - 2 * π * n * z.im =
              n * (n * (-π * τj.im) - 2 * π * z.im) by ring]
      refine tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ ?_)
      exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const
        (mul_pos_of_neg_of_neg (neg_lt_zero.mpr pi_pos) hτj))
    · -- case im τj = 0: 3-way split according to `im z`
      simp_rw [← summable_norm_iff (E := ℂ), norm_jacobiTheta₂_term, hτj, mul_zero, zero_sub] at h
      rcases lt_trichotomy (im z) 0 with hz | hz | hz
      · replace h := (h.comp_injective (fun a b ↦ Int.ofNat_inj.mp)).tendsto_atTop_zero
        simp_rw [Function.comp_def, Int.cast_natCast] at h
        refine atTop_neBot.ne (disjoint_self.mp <| h.disjoint (disjoint_nhds_atTop 0) ?_)
        refine tendsto_exp_atTop.comp ?_
        simp only [tendsto_neg_atTop_iff, mul_assoc]
        apply Filter.Tendsto.const_mul_atBot two_pos
        exact (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hz).const_mul_atBot pi_pos
      · revert h
        simpa only [hz, mul_zero, neg_zero, Real.exp_zero, summable_const_iff] using one_ne_zero
      · have : ((-↑·) : ℕ → ℤ).Injective := fun _ _ ↦ by simp only [neg_inj, Nat.cast_inj, imp_self]
        replace h := (h.comp_injective this).tendsto_atTop_zero
        simp_rw [Function.comp_def, Int.cast_neg, Int.cast_natCast, mul_neg, neg_mul, neg_neg] at h
        refine atTop_neBot.ne (disjoint_self.mp <| h.disjoint (disjoint_nhds_atTop 0) ?_)
        exact tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop.const_mul_atTop
          (mul_pos two_pos pi_pos)).atTop_mul_const hz)

lemma norm_jacobiTheta₂_term_fderiv_le (n : ℤ) (z τj : ℂ) :
    ‖jacobiTheta₂_term_fderiv n z τj‖ ≤ 3 * π * |n| ^ 2 * ‖jacobiTheta₂_term n z τj‖ := by
  -- this is slow to elaborate so do it once and reuse:
  have hns (a : ℂ) (f : (ℂ × ℂ) →L[ℂ] ℂ) : ‖a • f‖ = ‖a‖ * ‖f‖ := norm_smul a f
  rw [jacobiTheta₂_term_fderiv, jacobiTheta₂_term, hns,
    mul_comm _ ‖cexp _‖, (by norm_num : (3 : ℝ) = 2 + 1), add_mul, add_mul]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _)
  · simp_rw [hns, norm_mul, ← ofReal_ofNat, ← ofReal_intCast,
      norm_real, norm_of_nonneg zero_le_two, Real.norm_of_nonneg pi_pos.le, norm_I, mul_one,
      Real.norm_eq_abs, ← Int.cast_abs, ← Int.cast_pow]
    grw [ContinuousLinearMap.norm_fst_le, mul_one, ← Int.le_self_sq]
  · simp_rw [hns, norm_mul, one_mul, norm_I, mul_one,
      norm_real, norm_of_nonneg pi_pos.le, ← ofReal_intCast, ← ofReal_pow, norm_real,
      Real.norm_eq_abs, Int.cast_abs, abs_pow]
    apply mul_le_of_le_one_right (mul_nonneg pi_pos.le (pow_nonneg (abs_nonneg _) _))
    exact ContinuousLinearMap.norm_snd_le ..

lemma norm_jacobiTheta₂_term_fderiv_ge (n : ℤ) (z τj : ℂ) :
    π * |n| ^ 2 * ‖jacobiTheta₂_term n z τj‖ ≤ ‖jacobiTheta₂_term_fderiv n z τj‖ := by
  have : ‖(jacobiTheta₂_term_fderiv n z τj) (0, 1)‖ ≤ ‖jacobiTheta₂_term_fderiv n z τj‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    simp_rw [Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one, mul_one, le_refl]
  refine le_trans ?_ this
  simp_rw [jacobiTheta₂_term_fderiv, jacobiTheta₂_term, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Pi.smul_apply, smul_zero, zero_add,
    smul_eq_mul, mul_one, mul_comm _ ‖cexp _‖, norm_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (norm_nonneg _)
  simp_rw [norm_real, norm_of_nonneg pi_pos.le, norm_I, mul_one,
    Int.cast_abs, ← norm_intCast, norm_pow]

lemma summable_jacobiTheta₂_term_fderiv_iff (z τj : ℂ) :
    Summable (jacobiTheta₂_term_fderiv · z τj) ↔ 0 < im τj := by
  constructor
  · rw [← summable_jacobiTheta₂_term_iff (z := z)]
    intro h
    have := h.norm
    refine this.of_norm_bounded_eventually ?_
    have : ∀ᶠ (n : ℤ) in cofinite, n ≠ 0 :=
      Int.cofinite_eq ▸ (mem_sup.mpr ⟨eventually_ne_atBot 0, eventually_ne_atTop 0⟩)
    filter_upwards [this] with n hn
    refine le_trans ?_ (norm_jacobiTheta₂_term_fderiv_ge n z τj)
    apply le_mul_of_one_le_left (norm_nonneg _)
    refine one_le_pi_div_two.trans (mul_le_mul_of_nonneg_left ?_ pi_pos.le)
    refine (by norm_num : 2⁻¹ ≤ (1 : ℝ)).trans ?_
    rw [one_le_sq_iff_one_le_abs, ← Int.cast_abs, abs_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hn
  · intro hτj
    refine ((summable_pow_mul_jacobiTheta₂_term_bound
      |z.im| hτj 2).mul_left (3 * π)).of_norm_bounded (fun n ↦ ?_)
    refine (norm_jacobiTheta₂_term_fderiv_le n z τj).trans
      (?_ : 3 * π * |n| ^ 2 * ‖jacobiTheta₂_term n z τj‖ ≤ _)
    simp_rw [mul_assoc (3 * π)]
    refine mul_le_mul_of_nonneg_left ?_ (mul_pos (by simp : 0 < (3 : ℝ)) pi_pos).le
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Int.cast_nonneg.mpr (abs_nonneg _)) _)
    exact norm_jacobiTheta₂_term_le hτj le_rfl le_rfl n

lemma summable_jacobiTheta₂'_term_iff (z τj : ℂ) :
    Summable (jacobiTheta₂'_term · z τj) ↔ 0 < im τj := by
  constructor
  · rw [← summable_jacobiTheta₂_term_iff (z := z)]
    refine fun h ↦ (h.norm.mul_left (2 * π)⁻¹).of_norm_bounded_eventually ?_
    have : ∀ᶠ (n : ℤ) in cofinite, n ≠ 0 :=
      Int.cofinite_eq ▸ (mem_sup.mpr ⟨eventually_ne_atBot 0, eventually_ne_atTop 0⟩)
    filter_upwards [this] with n hn
    rw [jacobiTheta₂'_term, norm_mul, ← mul_assoc]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    simp_rw [norm_mul, norm_I, norm_real, mul_one, norm_of_nonneg pi_pos.le,
      ← ofReal_ofNat, norm_real, norm_of_nonneg two_pos.le, ← ofReal_intCast, norm_real,
      Real.norm_eq_abs, ← Int.cast_abs, ← mul_assoc _ (2 * π),
      inv_mul_cancel₀ (mul_pos two_pos pi_pos).ne', one_mul]
    rw [← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hn
  · refine fun hτj ↦ ((summable_pow_mul_jacobiTheta₂_term_bound
      |z.im| hτj 1).mul_left (2 * π)).of_norm_bounded (fun n ↦ ?_)
    rw [jacobiTheta₂'_term, norm_mul, ← mul_assoc, pow_one]
    refine mul_le_mul (le_of_eq ?_) (norm_jacobiTheta₂_term_le hτj le_rfl le_rfl n)
      (norm_nonneg _) (by positivity)
    simp_rw [norm_mul, Complex.norm_two, norm_I, Complex.norm_of_nonneg pi_pos.le,
      norm_intCast, mul_one, Int.cast_abs]

end term_bounds

/-!
## Definitions of the functions
-/

/-- The two-variable Jacobi theta function,
`θ z τj = ∑' (n : ℤ), cexp (2 * π * I * n * z + π * I * n ^ 2 * τj)`.
-/
def jacobiTheta₂ (z τj : ℂ) : ℂ := ∑' n : ℤ, jacobiTheta₂_term n z τj

/-- Fréchet derivative of the two-variable Jacobi theta function. -/
def jacobiTheta₂_fderiv (z τj : ℂ) : ℂ × ℂ →L[ℂ] ℂ := ∑' n : ℤ, jacobiTheta₂_term_fderiv n z τj

/-- The `z`-derivative of the Jacobi theta function,
`θ' z τj = ∑' (n : ℤ), 2 * π * I * n * cexp (2 * π * I * n * z + π * I * n ^ 2 * τj)`.
-/
def jacobiTheta₂' (z τj : ℂ) := ∑' n : ℤ, jacobiTheta₂'_term n z τj

lemma hasSum_jacobiTheta₂_term (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    HasSum (fun n ↦ jacobiTheta₂_term n z τj) (jacobiTheta₂ z τj) :=
  ((summable_jacobiTheta₂_term_iff z τj).mpr hτj).hasSum

lemma hasSum_jacobiTheta₂_term_fderiv (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    HasSum (fun n ↦ jacobiTheta₂_term_fderiv n z τj) (jacobiTheta₂_fderiv z τj) :=
  ((summable_jacobiTheta₂_term_fderiv_iff z τj).mpr hτj).hasSum

lemma hasSum_jacobiTheta₂'_term (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    HasSum (fun n ↦ jacobiTheta₂'_term n z τj) (jacobiTheta₂' z τj) :=
  ((summable_jacobiTheta₂'_term_iff z τj).mpr hτj).hasSum

lemma jacobiTheta₂_undef (z : ℂ) {τj : ℂ} (hτj : im τj ≤ 0) : jacobiTheta₂ z τj = 0 := by
  apply tsum_eq_zero_of_not_summable
  rw [summable_jacobiTheta₂_term_iff]
  exact not_lt.mpr hτj

lemma jacobiTheta₂_fderiv_undef (z : ℂ) {τj : ℂ} (hτj : im τj ≤ 0) : jacobiTheta₂_fderiv z τj = 0 := by
  apply tsum_eq_zero_of_not_summable
  rw [summable_jacobiTheta₂_term_fderiv_iff]
  exact not_lt.mpr hτj

lemma jacobiTheta₂'_undef (z : ℂ) {τj : ℂ} (hτj : im τj ≤ 0) : jacobiTheta₂' z τj = 0 := by
  apply tsum_eq_zero_of_not_summable
  rw [summable_jacobiTheta₂'_term_iff]
  exact not_lt.mpr hτj

/-!
## Derivatives and continuity
-/

lemma hasFDerivAt_jacobiTheta₂ (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    HasFDerivAt (fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (jacobiTheta₂_fderiv z τj) (z, τj) := by
  obtain ⟨T, hT, hτj'⟩ := exists_between hτj
  obtain ⟨S, hz⟩ := exists_gt |im z|
  let V := {u | |im u| < S} ×ˢ {v | T < im v}
  have hVo : IsOpen V := by
    refine ((_root_.continuous_abs.comp continuous_im).isOpen_preimage _ isOpen_Iio).prod ?_
    exact continuous_im.isOpen_preimage _ isOpen_Ioi
  have hVmem : (z, τj) ∈ V := ⟨hz, hτj'⟩
  have hVp : IsPreconnected V := by
    refine (Convex.isPreconnected ?_).prod (convex_halfSpace_im_gt T).isPreconnected
    simpa only [abs_lt] using (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  let f : ℤ → ℂ × ℂ → ℂ := fun n p ↦ jacobiTheta₂_term n p.1 p.2
  let f' : ℤ → ℂ × ℂ → ℂ × ℂ →L[ℂ] ℂ := fun n p ↦ jacobiTheta₂_term_fderiv n p.1 p.2
  have hf (n : ℤ) : ∀ p ∈ V, HasFDerivAt (f n) (f' n p) p :=
    fun p _ ↦ hasFDerivAt_jacobiTheta₂_term n p.1 p.2
  let u : ℤ → ℝ := fun n ↦ 3 * π * |n| ^ 2 * Real.exp (-π * (T * n ^ 2 - 2 * S * |n|))
  have hu : ∀ (n : ℤ), ∀ x ∈ V, ‖f' n x‖ ≤ u n := by
    refine fun n p hp ↦ (norm_jacobiTheta₂_term_fderiv_le n p.1 p.2).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_jacobiTheta₂_term_le hT (le_of_lt hp.1) (le_of_lt hp.2) n
  have hu_sum : Summable u := by
    simp_rw [u, mul_assoc (3 * π)]
    exact (summable_pow_mul_jacobiTheta₂_term_bound S hT 2).mul_left _
  have hf_sum : Summable fun n : ℤ ↦ f n (z, τj) := by
    refine (summable_pow_mul_jacobiTheta₂_term_bound S hT 0).of_norm_bounded ?_
    simpa only [pow_zero, one_mul] using norm_jacobiTheta₂_term_le hT hz.le hτj'.le
  simpa only [jacobiTheta₂, jacobiTheta₂_fderiv, f, f'] using
    hasFDerivAt_tsum_of_isPreconnected hu_sum hVo hVp hf hu hVmem hf_sum hVmem

lemma continuousAt_jacobiTheta₂ (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    ContinuousAt (fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (z, τj) :=
  (hasFDerivAt_jacobiTheta₂ z hτj).continuousAt

/-- Differentiability of `Θ z τj` in `z`, for fixed `τj`. -/
lemma differentiableAt_jacobiTheta₂_fst (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    DifferentiableAt ℂ (jacobiTheta₂ · τj) z :=
  ((hasFDerivAt_jacobiTheta₂ z hτj).comp (𝕜 := ℂ) z (hasFDerivAt_prodMk_left z τj) :).differentiableAt

/-- Differentiability of `Θ z τj` in `τj`, for fixed `z`. -/
lemma differentiableAt_jacobiTheta₂_snd (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    DifferentiableAt ℂ (jacobiTheta₂ z) τj :=
  ((hasFDerivAt_jacobiTheta₂ z hτj).comp τj (hasFDerivAt_prodMk_right z τj)).differentiableAt

lemma hasDerivAt_jacobiTheta₂_fst (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    HasDerivAt (jacobiTheta₂ · τj) (jacobiTheta₂' z τj) z := by
  -- This proof is annoyingly fiddly, because of the need to commute "evaluation at a point"
  -- through infinite sums of continuous linear maps.
  let eval_fst_CLM : (ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
  { toFun := fun f ↦ f (1, 0)
    cont := continuous_id'.clm_apply continuous_const
    map_add' := by simp only [ContinuousLinearMap.add_apply, forall_const]
    map_smul' := by simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, forall_const] }
  have step1 : HasSum (fun n ↦ (jacobiTheta₂_term_fderiv n z τj) (1, 0))
      ((jacobiTheta₂_fderiv z τj) (1, 0)) := by
    apply eval_fst_CLM.hasSum (hasSum_jacobiTheta₂_term_fderiv z hτj)
  have step2 (n : ℤ) : (jacobiTheta₂_term_fderiv n z τj) (1, 0) = jacobiTheta₂'_term n z τj := by
    simp only [jacobiTheta₂_term_fderiv, smul_add, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_fst', Pi.smul_apply, smul_eq_mul,
      mul_one, ContinuousLinearMap.coe_snd', mul_zero, add_zero, jacobiTheta₂'_term,
      jacobiTheta₂_term, mul_comm _ (cexp _)]
  rw [funext step2] at step1
  have step3 : HasDerivAt (fun x ↦ jacobiTheta₂ x τj) ((jacobiTheta₂_fderiv z τj) (1, 0)) z :=
    (((hasFDerivAt_jacobiTheta₂ z hτj).comp z (hasFDerivAt_prodMk_left z τj)).hasDerivAt :)
  rwa [← step1.tsum_eq] at step3

lemma continuousAt_jacobiTheta₂' (z : ℂ) {τj : ℂ} (hτj : 0 < im τj) :
    ContinuousAt (fun p : ℂ × ℂ ↦ jacobiTheta₂' p.1 p.2) (z, τj) := by
  obtain ⟨T, hT, hτj'⟩ := exists_between hτj
  obtain ⟨S, hz⟩ := exists_gt |im z|
  let V := {u | |im u| < S} ×ˢ {v | T < im v}
  have hVo : IsOpen V := ((_root_.continuous_abs.comp continuous_im).isOpen_preimage _
    isOpen_Iio).prod (continuous_im.isOpen_preimage _ isOpen_Ioi)
  refine ContinuousOn.continuousAt ?_ (hVo.mem_nhds ⟨hz, hτj'⟩)
  let u (n : ℤ) : ℝ := 2 * π * |n| * rexp (-π * (T * n ^ 2 - 2 * S * |n|))
  have hu : Summable u := by simpa only [u, mul_assoc, pow_one]
      using (summable_pow_mul_jacobiTheta₂_term_bound S hT 1).mul_left (2 * π)
  refine continuousOn_tsum (fun n ↦ ?_) hu (fun n ⟨z', τj'⟩ ⟨hz', hτj'⟩ ↦ ?_)
  · apply Continuous.continuousOn
    unfold jacobiTheta₂'_term jacobiTheta₂_term
    fun_prop
  · exact norm_jacobiTheta₂'_term_le hT (le_of_lt hz') (le_of_lt hτj') n

/-!
## Periodicity and conjugation
-/

/-- The two-variable Jacobi theta function is periodic in `τj` with period 2. -/
lemma jacobiTheta₂_add_right (z τj : ℂ) : jacobiTheta₂ z (τj + 2) = jacobiTheta₂ z τj := by
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [jacobiTheta₂_term, Complex.exp_add]
  suffices cexp (π * I * n ^ 2 * 2 : ℂ) = 1 by rw [mul_add, Complex.exp_add, this, mul_one]
  rw [(by push_cast; ring : (π * I * n ^ 2 * 2 : ℂ) = (n ^ 2 :) * (2 * π * I)), exp_int_mul,
    exp_two_pi_mul_I, one_zpow]

/-- The two-variable Jacobi theta function is periodic in `z` with period 1. -/
lemma jacobiTheta₂_add_left (z τj : ℂ) : jacobiTheta₂ (z + 1) τj = jacobiTheta₂ z τj := by
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [jacobiTheta₂_term, mul_add, Complex.exp_add, mul_one, mul_comm _ (n : ℂ),
    exp_int_mul_two_pi_mul_I, mul_one]

/-- The two-variable Jacobi theta function is quasi-periodic in `z` with period `τj`. -/
lemma jacobiTheta₂_add_left' (z τj : ℂ) :
    jacobiTheta₂ (z + τj) τj = cexp (-π * I * (τj + 2 * z)) * jacobiTheta₂ z τj := by
  conv_rhs => rw [jacobiTheta₂, ← tsum_mul_left, ← (Equiv.addRight 1).tsum_eq]
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [jacobiTheta₂_term, ← Complex.exp_add, Equiv.coe_addRight, Int.cast_add]
  ring_nf

/-- The two-variable Jacobi theta function is even in `z`. -/
@[simp]
lemma jacobiTheta₂_neg_left (z τj : ℂ) : jacobiTheta₂ (-z) τj = jacobiTheta₂ z τj := by
  conv_lhs => rw [jacobiTheta₂, ← Equiv.tsum_eq (Equiv.neg ℤ)]
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [jacobiTheta₂_term, Equiv.neg_apply, Int.cast_neg, neg_sq, mul_assoc, neg_mul_neg]

lemma jacobiTheta₂_conj (z τj : ℂ) :
    conj (jacobiTheta₂ z τj) = jacobiTheta₂ (conj z) (-conj τj) := by
  rw [← jacobiTheta₂_neg_left, jacobiTheta₂, conj_tsum]
  congr 2 with n
  simp only [jacobiTheta₂_term, mul_neg, ← exp_conj, map_add, map_neg, map_mul, map_ofNat,
    conj_ofReal, conj_I, map_intCast, neg_mul, neg_neg, map_pow]

lemma jacobiTheta₂'_add_right (z τj : ℂ) : jacobiTheta₂' z (τj + 2) = jacobiTheta₂' z τj := by
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [jacobiTheta₂'_term, jacobiTheta₂_term, Complex.exp_add]
  suffices cexp (π * I * n ^ 2 * 2 : ℂ) = 1 by rw [mul_add, Complex.exp_add, this, mul_one]
  rw [(by push_cast; ring : (π * I * n ^ 2 * 2 : ℂ) = (n ^ 2 :) * (2 * π * I)), exp_int_mul,
    exp_two_pi_mul_I, one_zpow]

lemma jacobiTheta₂'_add_left (z τj : ℂ) : jacobiTheta₂' (z + 1) τj = jacobiTheta₂' z τj := by
  unfold jacobiTheta₂' jacobiTheta₂'_term jacobiTheta₂_term
  refine tsum_congr (fun n ↦ ?_)
  simp only [mul_add, Complex.exp_add, mul_one, mul_comm _ (n : ℂ), exp_int_mul_two_pi_mul_I,
    mul_one]

lemma jacobiTheta₂'_add_left' (z τj : ℂ) :
    jacobiTheta₂' (z + τj) τj =
      cexp (-π * I * (τj + 2 * z)) * (jacobiTheta₂' z τj - 2 * π * I * jacobiTheta₂ z τj) := by
  rcases le_or_gt τj.im 0 with hτj | hτj
  · simp_rw [jacobiTheta₂_undef _ hτj, jacobiTheta₂'_undef _ hτj, mul_zero, sub_zero, mul_zero]
  have (n : ℤ) : jacobiTheta₂'_term n (z + τj) τj =
      cexp (-π * I * (τj + 2 * z)) * (jacobiTheta₂'_term (n + 1) z τj -
      2 * π * I * jacobiTheta₂_term (n + 1) z τj) := by
    simp only [jacobiTheta₂'_term, jacobiTheta₂_term]
    conv_rhs => rw [← sub_mul, mul_comm, mul_assoc, ← Complex.exp_add, Int.cast_add, Int.cast_one,
      mul_add, mul_one, add_sub_cancel_right]
    congr 2
    ring
  rw [jacobiTheta₂', funext this, tsum_mul_left, ← (Equiv.subRight (1 : ℤ)).tsum_eq]
  simp only [jacobiTheta₂, jacobiTheta₂', Equiv.subRight_apply, sub_add_cancel,
    (hasSum_jacobiTheta₂'_term z hτj).summable.tsum_sub
    ((hasSum_jacobiTheta₂_term z hτj).summable.mul_left _), tsum_mul_left]

lemma jacobiTheta₂'_neg_left (z τj : ℂ) : jacobiTheta₂' (-z) τj = -jacobiTheta₂' z τj := by
  rw [jacobiTheta₂', jacobiTheta₂', ← tsum_neg, ← (Equiv.neg ℤ).tsum_eq]
  congr 1 with n
  simp only [jacobiTheta₂'_term, jacobiTheta₂_term]
  rw [Equiv.neg_apply, ← neg_mul]
  push_cast
  ring_nf

lemma jacobiTheta₂'_conj (z τj : ℂ) :
    conj (jacobiTheta₂' z τj) = jacobiTheta₂' (conj z) (-conj τj) := by
  rw [← neg_inj, ← jacobiTheta₂'_neg_left, jacobiTheta₂', jacobiTheta₂', conj_tsum, ← tsum_neg]
  congr 1 with n
  simp_rw [jacobiTheta₂'_term, jacobiTheta₂_term, map_mul, ← Complex.exp_conj, map_add, map_mul,
    ← ofReal_intCast, ← ofReal_ofNat, map_pow, conj_ofReal, conj_I]
  ring_nf

/-!
## Functional equations
-/

/-- The functional equation for the Jacobi theta function: `jacobiTheta₂ z τj` is an explicit factor
times `jacobiTheta₂ (z / τj) (-1 / τj)`. This is the key lemma behind the proof of the functional
equation for L-series of even Dirichlet characters. -/
theorem jacobiTheta₂_functional_equation (z τj : ℂ) : jacobiTheta₂ z τj =
    1 / (-I * τj) ^ (1 / 2 : ℂ) * cexp (-π * I * z ^ 2 / τj) * jacobiTheta₂ (z / τj) (-1 / τj) := by
  rcases le_or_gt (im τj) 0 with hτj | hτj
  · have : (-1 / τj).im ≤ 0 := by
      rw [neg_div, neg_im, one_div, inv_im, neg_nonpos]
      exact div_nonneg (neg_nonneg.mpr hτj) (normSq_nonneg τj)
    rw [jacobiTheta₂_undef z hτj, jacobiTheta₂_undef _ this, mul_zero]
  unfold jacobiTheta₂ jacobiTheta₂_term
  have h2 : 0 < (-I * τj).re := by
    simpa only [neg_mul, neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg] using hτj
  calc
  _ = ∑' n : ℤ, cexp (-π * (-I * τj) * ↑n ^ 2 + 2 * π * (I * z) * ↑n) :=
    tsum_congr (fun n ↦ by ring_nf)
  _ = 1 / (-I * τj) ^ (1 / 2 : ℂ) * ∑' (n : ℤ), cexp (-π / (-I * τj) * (n + I * (I * z)) ^ 2) := by
    rw [tsum_exp_neg_quadratic h2]
  _ = 1 / (-I * τj) ^ (1 / 2 : ℂ) * cexp (π * I * (-1 / τj) * z ^ 2) *
      ∑' (n : ℤ), cexp (2 * π * I * n * (z / τj) + π * I * n ^ 2 * (-1 / τj)) := by
    simp_rw [mul_assoc _ (cexp _), ← tsum_mul_left (a := cexp _), ← Complex.exp_add]
    congr 2 with n : 1; congr 1
    field_simp
    ring_nf
    simp_rw [I_sq, I_pow_four]
    ring_nf
  _ = _ := by
    congr 3
    ring

/-- The functional equation for the derivative of the Jacobi theta function, relating
`jacobiTheta₂' z τj` to `jacobiTheta₂' (z / τj) (-1 / τj)`. This is the key lemma behind the proof of
the functional equation for L-series of odd Dirichlet characters. -/
theorem jacobiTheta₂'_functional_equation (z τj : ℂ) :
    jacobiTheta₂' z τj = 1 / (-I * τj) ^ (1 / 2 : ℂ) * cexp (-π * I * z ^ 2 / τj) / τj *
      (jacobiTheta₂' (z / τj) (-1 / τj) - 2 * π * I * z * jacobiTheta₂ (z / τj) (-1 / τj)) := by
  rcases le_or_gt (im τj) 0 with hτj | hτj
  · rw [jacobiTheta₂'_undef z hτj, jacobiTheta₂'_undef, jacobiTheta₂_undef, mul_zero,
      sub_zero, mul_zero] <;>
    rw [neg_div, neg_im, one_div, inv_im, neg_nonpos] <;>
    exact div_nonneg (neg_nonneg.mpr hτj) (normSq_nonneg τj)
  have hτj' : 0 < (-1 / τj).im := by
    rw [div_eq_mul_inv, neg_one_mul, neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hτj (normSq_pos.mpr (fun h ↦ lt_irrefl 0 (zero_im ▸ h ▸ hτj)))
  have hj : HasDerivAt (fun w ↦ jacobiTheta₂ (w / τj) (-1 / τj))
      ((1 / τj) * jacobiTheta₂' (z / τj) (-1 / τj)) z := by
    have := hasDerivAt_jacobiTheta₂_fst (z / τj) hτj'
    simpa only [mul_comm, one_div] using this.comp z (hasDerivAt_mul_const τj⁻¹)
  calc
  _ = deriv (jacobiTheta₂ · τj) z := (hasDerivAt_jacobiTheta₂_fst z hτj).deriv.symm
  _ = deriv (fun z ↦ 1 / (-I * τj) ^ (1 / 2 : ℂ) *
        cexp (-π * I * z ^ 2 / τj) * jacobiTheta₂ (z / τj) (-1 / τj)) z := by
    rw [funext (jacobiTheta₂_functional_equation · τj)]
  _ = 1 / (-I * τj) ^ (1 / 2 : ℂ) *
        deriv (fun z ↦ cexp (-π * I * z ^ 2 / τj) * jacobiTheta₂ (z / τj) (-1 / τj)) z := by
    simp_rw [mul_assoc, deriv_const_mul_field]
  _ = 1 / (-I * τj) ^ (1 / 2 : ℂ) *
        (deriv (fun z ↦ cexp (-π * I * z ^ 2 / τj)) z * jacobiTheta₂ (z / τj) (-1 / τj)
         + cexp (-π * I * z ^ 2 / τj) * deriv (fun z ↦ jacobiTheta₂ (z / τj) (-1 / τj)) z) := by
    rw [deriv_fun_mul _ hj.differentiableAt]
    exact (((differentiableAt_pow 2).const_mul _).mul_const _).cexp
  _ = _ := by
    rw [hj.deriv]
    simp only [div_eq_mul_inv _ τj]
    rw [deriv_cexp (((differentiableAt_pow _).const_mul _).mul_const _), mul_comm,
      deriv_mul_const_field, deriv_const_mul_field, deriv_pow_field]
    ring_nf
