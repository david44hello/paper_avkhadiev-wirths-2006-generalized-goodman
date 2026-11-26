-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Defs

noncomputable section
open Set

namespace Goodman

private def cayley (z : ℂ) : ℂ := (1 - z) / (1 + z)

private def realCayley (x : ℝ) : ℝ := (1 - x) / (1 + x)

private lemma cayley_ofReal (x : ℝ) : cayley x = (realCayley x : ℂ) := by
  simp [cayley, realCayley]

private lemma denom_disk {z : ℂ} (hz : z ∈ disk) : 1 + z ≠ 0 := by
  have h : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have : z = -1 := by linear_combination he
  simp_all

private lemma denom_right {z : ℂ} (hz : 0 < z.re) : 1 + z ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  simp at h
  linarith

private lemma cayley_denom {z : ℂ} (hz : 1 + z ≠ 0) : 1 + cayley z ≠ 0 := by
  unfold cayley
  field_simp [hz]
  ring_nf
  norm_num
  exact hz

private lemma cayley_invol {z : ℂ} (hz : 1 + z ≠ 0) : cayley (cayley z) = z := by
  have h := cayley_denom hz
  unfold cayley at *
  field_simp [hz, h]
  ring

private lemma cayley_re_pos_iff {z : ℂ} (hz : 1 + z ≠ 0) :
    0 < (cayley z).re ↔ z ∈ disk := by
  have h : (cayley z).re = (1 - Complex.normSq z) / Complex.normSq (1 + z) := by
    simp only [cayley, Complex.div_re, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_sub,
      zero_add, ← add_div]
    congr 1
    rw [Complex.normSq_apply]
    ring
  rw [h, div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hz), Complex.normSq_eq_norm_sq]
  simp only [disk, Metric.mem_ball, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]

private lemma cayley_right {z : ℂ} (hz : z ∈ disk) : 0 < (cayley z).re :=
  (cayley_re_pos_iff (denom_disk hz)).2 hz

private lemma cayley_disk {s : ℂ} (hs : 0 < s.re) : cayley s ∈ disk := by
  apply (cayley_re_pos_iff (cayley_denom (denom_right hs))).1
  rwa [cayley_invol (denom_right hs)]

private lemma cayley_analytic {z : ℂ} (hz : 1 + z ≠ 0) : AnalyticAt ℂ cayley z := by
  unfold cayley
  fun_prop (disch := assumption)

-- On the real axis the Cayley transform reverses the order of the endpoints.
private lemma realCayley_lt_iff {x p : ℝ} (hx : 0 < x) (hp : 0 < p) :
    realCayley x < p ↔ realCayley p < x := by
  unfold realCayley
  rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith only [h, mul_comm x p]

private def rightSlit (a : ℝ) (s : ℂ) : Prop :=
  0 < s.re ∧ (s.im = 0 → a < s.re)

private lemma cayley_slit_iff {p : ℝ} (hp : 0 < p) {s : ℂ} (hs : 0 < s.re) :
    cayley s ∈ slitDisk p ↔ rightSlit (realCayley p) s := by
  have hreal (hi : s.im = 0) : cayley s = (realCayley s.re : ℂ) := by
    have he : (s.re : ℂ) = s := Complex.ext (by simp) (by simp [hi])
    exact (congrArg cayley he.symm).trans (cayley_ofReal _)
  constructor
  · intro hz
    refine ⟨hs, fun hi => (realCayley_lt_iff hs hp).1 ?_⟩
    by_contra! h
    apply hz.2
    refine ⟨realCayley s.re, ⟨h, ?_⟩, (hreal hi).symm⟩
    unfold realCayley
    rw [div_lt_iff₀ (by linarith)]
    linarith
  · intro h
    refine ⟨cayley_disk hs, ?_⟩
    rintro ⟨x, hx, he⟩
    change (x : ℂ) = cayley s at he
    have he' : (realCayley x : ℂ) = s := by
      rw [← cayley_ofReal, he, cayley_invol (denom_right hs)]
    have hi : s.im = 0 := by rw [← he']; rfl
    have hx' : x = realCayley s.re := Complex.ofReal_injective (he.trans (hreal hi))
    exact (not_lt_of_ge hx.1) (hx' ▸ (realCayley_lt_iff hs hp).2 (h.2 hi))

private lemma cayley_rightSlit {p : ℝ} (hp : 0 < p) {z : ℂ} (hz : z ∈ slitDisk p) :
    rightSlit (realCayley p) (cayley z) := by
  apply (cayley_slit_iff hp (cayley_right hz.1)).1
  rwa [cayley_invol (denom_disk hz.1)]

private lemma sqrt_sq_value (z : ℂ) : (Complex.sqrt z)^2 = z :=
  Complex.cpow_nat_inv_pow z (n := 2) (by decide)

private lemma sqrt_right {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re, Real.sqrt_pos]
  rcases Complex.mem_slitPlane_iff.mp hz with h | h
  · linarith [norm_nonneg z]
  · linarith [(abs_lt.mp (Complex.abs_re_lt_norm.mpr h)).1]

private lemma right_sq_inj {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (h : s^2 = t^2) : s = t := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · rw [h, Complex.neg_re] at hs
    linarith

private lemma sq_re (z : ℂ) : (z^2).re = z.re^2 - z.im^2 := by
  simp [sq, Complex.mul_re]

private lemma sq_im (z : ℂ) : (z^2).im = 2 * z.re * z.im := by
  simp [sq, Complex.mul_im]
  ring

private def forwardArg (a r : ℝ) (s : ℂ) : ℂ := (s^2 - (a : ℂ)^2) / (r : ℂ)
private def inverseArg (a r : ℝ) (t : ℂ) : ℂ := (r : ℂ) * t^2 + (a : ℂ)^2

private lemma forwardArg_slit {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {s : ℂ}
    (hs : rightSlit a s) : forwardArg a r s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : s.im = 0
  · left
    simp [forwardArg, sq_re, Complex.sub_re, hi, div_pos_iff_of_pos_right hr]
    have h := pow_lt_pow_left₀ (hs.2 hi) ha.le (by decide : (2 : ℕ) ≠ 0)
    linarith
  · right
    simp [forwardArg, sq_im, Complex.sub_im, hr.ne', hs.1.ne', hi]

private lemma inverseArg_slit {a r : ℝ} (hr : 0 < r) {t : ℂ} (ht : 0 < t.re) :
    inverseArg a r t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : t.im = 0
  · left
    simp [inverseArg, Complex.add_re, Complex.mul_re, sq_re, hi]
    positivity
  · right
    simp [inverseArg, Complex.add_im, Complex.mul_im, sq_im, hr.ne', ht.ne', hi]

private def forwardRoot (a r : ℝ) (s : ℂ) : ℂ := Complex.sqrt (forwardArg a r s)
private def inverseRoot (a r : ℝ) (t : ℂ) : ℂ := Complex.sqrt (inverseArg a r t)

private lemma inverseRoot_rightSlit {a r : ℝ} (hr : 0 < r) {t : ℂ} (ht : 0 < t.re) :
    rightSlit a (inverseRoot a r t) := by
  let s := inverseRoot a r t
  have hs : 0 < s.re := sqrt_right (inverseArg_slit hr ht)
  have he : s^2 = inverseArg a r t := sqrt_sq_value _
  refine ⟨hs, ?_⟩
  change s.im = 0 → a < s.re
  intro hi
  have him := congrArg Complex.im he
  simp [sq_im, inverseArg, Complex.add_im, Complex.mul_im, hi, hr.ne', ht.ne'] at him
  have hre := congrArg Complex.re he
  simp [sq_re, inverseArg, Complex.add_re, Complex.mul_re, hi, him] at hre
  by_contra! h
  have hle := pow_le_pow_left₀ hs.le h 2
  linarith [mul_pos hr (sq_pos_of_pos ht)]

private lemma forward_analytic {a r : ℝ} {s : ℂ}
    (h : forwardArg a r s ∈ Complex.slitPlane) : AnalyticAt ℂ (forwardRoot a r) s := by
  apply (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane _ h).comp
    (f := forwardArg a r)
  unfold forwardArg
  fun_prop

private lemma inverse_analytic {a r : ℝ} {t : ℂ}
    (h : inverseArg a r t ∈ Complex.slitPlane) : AnalyticAt ℂ (inverseRoot a r) t := by
  apply (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane _ h).comp
    (f := inverseArg a r)
  unfold inverseArg
  fun_prop

private lemma cayley_sq_identity {z : ℂ} (hz : 1 + z ≠ 0) :
    (1 - (cayley z)^2) * (1 + z)^2 = 4*z := by
  unfold cayley
  field_simp [hz]
  ring

/-- The normalized slit map obtained by taking a principal square root in Cayley coordinates. -/
theorem exists_isSlitMap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ q, IsSlitMap p q := by
  let a := realCayley p
  let r := slitR p
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hr : 0 < r := by dsimp [r, slitR]; positivity
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpar : (r : ℂ) = 1 - (a : ℂ)^2 := by
    have h : r = 1 - a^2 := by
      dsimp [r, a, slitR, realCayley]
      field_simp [show 1 + p ≠ 0 by linarith]
      ring
    exact_mod_cast h
  let q := cayley ∘ forwardRoot a r ∘ cayley
  let χ := cayley ∘ inverseRoot a r ∘ cayley
  have hf {s : ℂ} (hs : rightSlit a s) : 0 < (forwardRoot a r s).re :=
    sqrt_right (forwardArg_slit ha hr hs)
  have hu {t : ℂ} (ht : 0 < t.re) : rightSlit a (inverseRoot a r t) :=
    inverseRoot_rightSlit hr ht
  refine ⟨q, ⟨?_, χ, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z hz
    have hs := cayley_rightSlit hp hz
    exact ((cayley_analytic (denom_right (hf hs))).comp
      (forward_analytic (forwardArg_slit ha hr hs))).comp (cayley_analytic (denom_disk hz.1))
  · intro w hw
    have ht := cayley_right hw
    exact ((cayley_analytic (denom_right (hu ht).1)).comp
      (inverse_analytic (inverseArg_slit (a := a) hr ht))).comp (cayley_analytic (denom_disk hw))
  · intro z hz
    exact cayley_disk (hf (cayley_rightSlit hp hz))
  · intro w hw
    have hs := hu (cayley_right hw)
    exact (cayley_slit_iff hp hs.1).2 hs
  · intro z hz
    have hs := cayley_rightSlit hp hz
    have ht := hf hs
    have he : inverseRoot a r (forwardRoot a r (cayley z)) = cayley z := by
      apply right_sq_inj (hu ht).1 hs.1
      rw [inverseRoot, sqrt_sq_value, inverseArg, forwardRoot, sqrt_sq_value, forwardArg]
      field_simp [hr']
      ring
    dsimp only [q, χ, Function.comp_apply]
    rw [cayley_invol (denom_right ht), he, cayley_invol (denom_disk hz.1)]
  · intro w hw
    have ht := cayley_right hw
    have hs := hu ht
    have he : forwardRoot a r (inverseRoot a r (cayley w)) = cayley w := by
      apply right_sq_inj (hf hs) ht
      rw [forwardRoot, sqrt_sq_value, forwardArg, inverseRoot, sqrt_sq_value, inverseArg]
      field_simp [hr']
      ring
    dsimp only [q, χ, Function.comp_apply]
    rw [cayley_invol (denom_right hs.1), he, cayley_invol (denom_disk hw)]
  · have h : forwardArg a r 1 = 1 := by
      simp [forwardArg, ← hpar, hr']
    simp [q, cayley, forwardRoot, h]
  · intro z hz
    have hs := cayley_rightSlit hp hz
    let t := forwardRoot a r (cayley z)
    have ht : 0 < t.re := hf hs
    have hq : cayley (q z) = t := cayley_invol (denom_right ht)
    have h₁ := cayley_sq_identity (denom_disk hz.1)
    have h₂ := cayley_sq_identity (denom_disk (cayley_disk ht))
    change (1 - (cayley (q z))^2) * (1 + q z)^2 = 4 * q z at h₂
    rw [hq] at h₂
    have h₃ : 1 - (cayley z)^2 = (r : ℂ) * (1 - t^2) := by
      have he : t^2 = forwardArg a r (cayley z) := sqrt_sq_value _
      rw [forwardArg, eq_div_iff hr'] at he
      linear_combination he - hpar
    change z * (1 + q z)^2 = (r : ℂ) * q z * (1 + z)^2
    linear_combination -(1 + q z)^2 / 4 * h₁ +
      (r : ℂ) * (1 + z)^2 / 4 * h₂ + (1 + z)^2 * (1 + q z)^2 / 4 * h₃

end Goodman
