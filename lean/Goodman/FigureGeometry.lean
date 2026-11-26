-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.SegmentGeometry
import Goodman.SlitMajorant

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

/-- Figure 3, including the pole in the spherical image and the normalization at zero. -/
theorem figure3_segment :
    extremal (1/2) '' disk = (realSlitSegment (-2) (-2/9))ᶜ ∧
    OnePoint.infty ∈ extremal (1/2) '' disk ∧ extremal (1/2) 0 = (0 : ℂ) := by
  have h := extremal_image_disk (p := 1/2) (by norm_num) (by norm_num)
  norm_num at h
  refine ⟨by simpa only [neg_div] using h, ⟨(1/2 : ℂ), by norm_num [disk], by norm_num [extremal]⟩, ?_⟩
  norm_num [extremal]

/-- Half the affine Joukowski coordinate on the closed slit. -/
def slitArcRe (p x : ℝ) : ℝ := (slitR p * (x + x⁻¹ + 2) - 2) / 2

/-- Upper (`s = 1`) and lower (`s = -1`) boundary values. -/
def slitArcPoint (p s x : ℝ) : ℂ :=
  ⟨slitArcRe p x, s * Real.sqrt (1 - slitArcRe p x ^ 2)⟩

theorem slitArcRe_tip {p : ℝ} (hp : 0 < p) : slitArcRe p p = 1 := by
  unfold slitArcRe slitR
  field_simp [hp.ne', (by linarith : 1+p ≠ 0)]
  ring

theorem slitArcRe_one (p : ℝ) : slitArcRe p 1 = 2 * slitR p - 1 := by
  simp [slitArcRe]
  ring

theorem slitArcRe_strictAnti {p : ℝ} (hp : 0 < p) :
    StrictAntiOn (slitArcRe p) (Icc p 1) := by
  intro x hx y hy hxy
  have hx0 := hp.trans_le hx.1
  have hy0 := hx0.trans hxy
  have hprod : x*y < 1 := (mul_le_of_le_one_right hx0.le hy.2).trans_lt (hxy.trans_le hy.2)
  have hJ : y + y⁻¹ < x + x⁻¹ := by
    field_simp [hx0, hy0]
    nlinarith [mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hprod)]
  unfold slitArcRe
  linarith [mul_lt_mul_of_pos_left (add_lt_add_right hJ 2) (slitR_pos hp)]

theorem slitArcRe_image {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    slitArcRe p '' Icc p 1 = Icc (2 * slitR p - 1) 1 := by
  have hc : ContinuousOn (slitArcRe p) (Icc p 1) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold slitArcRe
    fun_prop (disch := exact (hp.trans_le hx.1).ne')
  rw [hc.image_Icc_of_antitoneOn hp1 (slitArcRe_strictAnti hp).antitoneOn,
    slitArcRe_tip hp, slitArcRe_one]

private lemma slitArcRe_bounds {p x : ℝ} (hp : 0 < p) (hx : x ∈ Icc p 1) :
    -1 ≤ slitArcRe p x ∧ slitArcRe p x ≤ 1 := by
  have h := (slitArcRe_image hp (hx.1.trans hx.2)) ▸
    (mem_image_of_mem (slitArcRe p) hx)
  exact ⟨le_trans (by linarith [slitR_pos hp]) h.1, h.2⟩

private lemma q_norm {p : ℝ} {q : ℂ → ℂ} (hq : IsSlitMap p q) {z : ℂ}
    (hz : z ∈ slitDisk p) : ‖q z‖ < 1 := by
  obtain ⟨_, _, hm, _⟩ := hq.1.2
  exact mem_ball_zero_iff.mp (hm hz)

private lemma joukowski_im (z : ℂ) :
    (z + z⁻¹).im = z.im * (1 - 1 / Complex.normSq z) := by
  rw [Complex.add_im, Complex.inv_im]
  ring

private lemma joukowski_factor_neg {z : ℂ} (hz : z ≠ 0) (hd : ‖z‖ < 1) :
    1 - 1 / Complex.normSq z < 0 := by
  have h : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖z‖ - 1), mul_pos (sub_pos.mpr hd)
      (show 0 < 1 + ‖z‖ by positivity)]
  exact sub_neg.mpr ((lt_div_iff₀ (Complex.normSq_pos.mpr hz)).2 (by simpa using h))

/-- On either open bank the slit map preserves the sign of the imaginary part. -/
theorem slitMap_bank_sign {p s : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hq : IsSlitMap p q)
    {z : ℂ} (hz : z ∈ slitDisk p) (hs : 0 < s * z.im) : 0 < s * (q z).im := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hs
  have he := hq.2.2 z hz
  have hw0 : q z ≠ 0 := by
    intro h
    simp [h, hz0] at he
  have hj : q z + (q z)⁻¹ = (slitR p : ℂ) * (z + z⁻¹ + 2) - 2 := by
    field_simp [hz0, hw0]
    linear_combination he
  have hi := congrArg Complex.im hj
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, show (2 : ℂ).im = 0 by rfl, zero_mul, add_zero, sub_zero] at hi
  have hi' : (q z).im * (1 - 1 / Complex.normSq (q z)) =
      slitR p * (z.im * (1 - 1 / Complex.normSq z)) := by
    simpa only [← joukowski_im, Complex.add_im] using hi
  have hzneg := joukowski_factor_neg hz0 (mem_ball_zero_iff.mp hz.1)
  have hwneg := joukowski_factor_neg hw0 (q_norm hq hz)
  have hneg : (s * (q z).im) * (1 - 1 / Complex.normSq (q z)) < 0 := by
    calc
      _ = slitR p * ((s * z.im) * (1 - 1 / Complex.normSq z)) := by
        linear_combination s * hi'
      _ < 0 := mul_neg_of_pos_of_neg (slitR_pos hp) (mul_neg_of_pos_of_neg hs hzneg)
  exact pos_of_mul_neg_left hneg hwneg.le

/-- Limiting quadratic at a real point of the slit, before choosing a bank. -/
private lemma limit_quadratic {p x : ℝ} {q : ℂ → ℂ} {z : ℕ → ℂ} {w : ℂ}
    (hq : IsSlitMap p q) (hx : 0 < x) (hz : Tendsto z atTop (𝓝 (x : ℂ)))
    (hw : Tendsto (q ∘ z) atTop (𝓝 w)) (hmem : ∀ᶠ n in atTop, z n ∈ slitDisk p) :
    w^2 - 2 * (slitArcRe p x : ℂ) * w + 1 = 0 := by
  have he : (x : ℂ) * (1+w)^2 = (slitR p : ℂ) * w * (1+(x : ℂ))^2 :=
    tendsto_nhds_unique_of_eventuallyEq (hz.mul ((tendsto_const_nhds.add hw).pow 2))
      ((tendsto_const_nhds.mul hw).mul ((tendsto_const_nhds.add hz).pow 2))
      (hmem.mono fun n hn => hq.2.2 (z n) hn)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold slitArcRe
  push_cast
  field_simp [hx0]
  linear_combination he

private lemma height_sq {t : ℝ} (hl : -1 ≤ t) (hu : t ≤ 1) :
    Real.sqrt (1-t^2)^2 = 1-t^2 :=
  Real.sq_sqrt (by nlinarith [mul_nonneg (by linarith : 0 ≤ 1+t) (sub_nonneg.mpr hu)])

/-- The limiting polynomial factors at the two conjugate points of the circle. -/
private lemma quadratic_roots {w : ℂ} {t : ℝ} (hl : -1 ≤ t) (hu : t ≤ 1)
    (hw : w^2 - 2*(t : ℂ)*w + 1 = 0) :
    w = ⟨t, Real.sqrt (1-t^2)⟩ ∨ w = ⟨t, -Real.sqrt (1-t^2)⟩ := by
  let y := Real.sqrt (1-t^2)
  have hy : (y : ℂ)^2 = 1 - (t : ℂ)^2 := by exact_mod_cast height_sq hl hu
  have he : (w - ((t : ℂ) + y * Complex.I)) * (w - ((t : ℂ) - y * Complex.I)) = 0 := by
    linear_combination hw - (y : ℂ)^2 * Complex.I_sq + hy
  rcases mul_eq_zero.mp he with h | h
  · left
    rw [sub_eq_zero.mp h]
    apply Complex.ext <;> simp [y]
  · right
    rw [sub_eq_zero.mp h]
    apply Complex.ext <;> simp [y]

/-- The two approach regions are the portions of the slit disk above and below the real axis. -/
def slitBank (p s : ℝ) : Set ℂ := slitDisk p ∩ {z | 0 < s * z.im}

/-- The boundary value at every point of each bank, including the tip and the outer endpoint. -/
theorem slitMap_bank_limit {p s x : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hq : IsSlitMap p q)
    (hs : s = 1 ∨ s = -1) (hx : x ∈ Icc p 1) :
    Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 (slitArcPoint p s x)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact mem_closedBall_zero_iff.mpr (q_norm hq hz.1).le
  intro w _ hc
  obtain ⟨z, hw, hz⟩ := hc.exists_seq_tendsto
  have hm := hz.eventually self_mem_nhdsWithin
  have h := limit_quadratic hq (hp.trans_le hx.1) (tendsto_nhdsWithin_iff.mp hz).1 hw
    (hm.mono fun _ h => h.1)
  have hi : 0 ≤ s * w.im := by
    apply ge_of_tendsto (tendsto_const_nhds.mul (Complex.continuous_im.continuousAt.tendsto.comp hw))
    exact hm.mono fun _ h => (slitMap_bank_sign hp hq h.1 h.2).le
  obtain ⟨hl, hu⟩ := slitArcRe_bounds hp hx
  rcases quadratic_roots hl hu h with rfl | rfl <;> rcases hs with rfl | rfl <;>
    apply Complex.ext <;> simp [slitArcPoint] at hi ⊢ <;> linarith [Real.sqrt_nonneg (1-slitArcRe p x^2)]

/-- Both banks and every other approach through the slit disk have the same limit at the tip. -/
theorem slitMap_tip_limit {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hq : IsSlitMap p q) :
    Tendsto q (𝓝[slitDisk p] (p : ℂ)) (𝓝 1) := by
  apply (isCompact_closedBall (0 : ℂ) 1).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact mem_closedBall_zero_iff.mpr (q_norm hq hz).le
  intro w _ hc
  obtain ⟨z, hw, hz⟩ := hc.exists_seq_tendsto
  have h := limit_quadratic hq hp (tendsto_nhdsWithin_iff.mp hz).1 hw
    (hz.eventually self_mem_nhdsWithin)
  rw [slitArcRe_tip hp] at h
  have : (w - 1)^2 = 0 := by push_cast at h; linear_combination h
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)

/-- Each bank actually accumulates at every point of the closed slit. -/
theorem slitBank_neBot {p s x : ℝ} (hp : 0 < p) (hs : s = 1 ∨ s = -1)
    (hx : x ∈ Icc p 1) : NeBot (𝓝[slitBank p s] (x : ℂ)) := by
  let v := (s : ℂ) * Complex.I / 2
  have hv : ‖v‖ = 1/2 := by rcases hs with rfl | rfl <;> norm_num [v, norm_div]
  have hvi : s * v.im = 1/2 := by rcases hs with rfl | rfl <;> norm_num [v, Complex.div_im]
  have hx' : ‖(x : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_of_nonneg (hp.trans_le hx.1).le] using hx.2
  apply mem_closure_iff_nhdsWithin_neBot.mp
  apply closure_mono (s := openSegment ℝ (x : ℂ) v) _ (segment_subset_closure_openSegment
    (left_mem_segment ℝ (x : ℂ) v))
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  have hi : 0 < s * (a • (x : ℂ) + b • v).im := by
    simp only [Complex.add_im, Complex.smul_im, Complex.ofReal_im, smul_eq_mul, mul_zero, zero_add]
    nlinarith [mul_pos hb (show 0 < s * v.im by linarith)]
  refine ⟨⟨mem_ball_zero_iff.mpr ?_, ?_⟩, hi⟩
  · calc
      _ ≤ ‖a • (x : ℂ)‖ + ‖b • v‖ := norm_add_le _ _
      _ ≤ a * 1 + b * (1/2) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb, hv]
        exact add_le_add (mul_le_mul_of_nonneg_left hx' ha.le) le_rfl
      _ < 1 := by linarith
  · rintro ⟨r, _, hr⟩
    change (r : ℂ) = _ at hr
    rw [← hr] at hi
    simp at hi

/-- A point on the specified half of the unit circle is determined by its real coordinate. -/
private lemma circle_point {s t : ℝ} {w : ℂ} (hs : s = 1 ∨ s = -1)
    (hw : ‖w‖ = 1) (ht : w.re = t) (hi : 0 ≤ s*w.im) :
    w = ⟨t, s * Real.sqrt (1-t^2)⟩ := by
  have he := Complex.sq_norm w
  rw [hw, Complex.normSq_apply, ht] at he
  have he' : 1-t^2 = w.im^2 := by nlinarith
  rw [he', Real.sqrt_sq_eq_abs]
  apply Complex.ext ht
  rcases hs with rfl | rfl
  · simp [abs_of_nonneg (by simpa using hi : 0 ≤ w.im)]
  · have h : w.im ≤ 0 := by simpa using hi
    simp [abs_of_nonpos h]

private lemma slitArcPoint_norm {p s x : ℝ} (hp : 0 < p) (hs : s = 1 ∨ s = -1)
    (hx : x ∈ Icc p 1) : ‖slitArcPoint p s x‖ = 1 := by
  obtain ⟨hl, hu⟩ := slitArcRe_bounds hp hx
  have hn : Complex.normSq (slitArcPoint p s x) = 1 := by
    rw [slitArcPoint, Complex.normSq_mk]
    rcases hs with rfl | rfl <;> simp only [one_mul, neg_one_mul, neg_mul_neg] <;>
      nlinarith [height_sq hl hu]
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (slitArcPoint p s x)]

/-- With the outer endpoint included by its one-sided limit, each bank traces exactly its
half of the arc. The real part runs strictly down from 1 to `2 * slitR p - 1`. -/
theorem slitMap_bank_trace {p s : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hp1 : p < 1)
    (hq : IsSlitMap p q) (hs : s = 1 ∨ s = -1) (w : ℂ) :
    (∃ x ∈ Icc p 1, Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 w)) ↔
      ‖w‖ = 1 ∧ 2 * slitR p - 1 ≤ w.re ∧ 0 ≤ s*w.im := by
  constructor
  · rintro ⟨x, hx, h⟩
    have := slitBank_neBot hp hs hx
    obtain rfl := tendsto_nhds_unique h (slitMap_bank_limit hp hq hs hx)
    have hm := mem_image_of_mem (slitArcRe p) hx
    rw [slitArcRe_image hp hp1.le] at hm
    refine ⟨slitArcPoint_norm hp hs hx, hm.1, ?_⟩
    rcases hs with rfl | rfl <;> simp [slitArcPoint, Real.sqrt_nonneg]
  · rintro ⟨hw, hl, hi⟩
    have hu := (le_abs_self w.re).trans (Complex.abs_re_le_norm w)
    rw [hw] at hu
    obtain ⟨x, hx, he⟩ := (slitArcRe_image hp hp1.le).superset (show w.re ∈ Icc _ _ from ⟨hl, hu⟩)
    exact ⟨x, hx, (circle_point hs hw he.symm hi).symm ▸ slitMap_bank_limit hp hq hs hx⟩

/-- On the half-open slit of the paper the two outer arc endpoints occur only as limits at 1. -/
theorem slitMap_bank_trace_Ico {p s : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hp1 : p < 1)
    (hq : IsSlitMap p q) (hs : s = 1 ∨ s = -1) (w : ℂ) :
    (∃ x ∈ Ico p 1, Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 w)) ↔
      ‖w‖ = 1 ∧ 2 * slitR p - 1 < w.re ∧ 0 ≤ s*w.im := by
  have coord {x : ℝ} (hx : x ∈ Icc p 1) (hw : Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 w)) :
      w.re = slitArcRe p x := by
    have := slitBank_neBot hp hs hx
    exact congrArg Complex.re (tendsto_nhds_unique hw (slitMap_bank_limit hp hq hs hx))
  constructor
  · rintro ⟨x, hx, h⟩
    have hx' : x ∈ Icc p 1 := ⟨hx.1, hx.2.le⟩
    obtain ⟨hw, _, hi⟩ := (slitMap_bank_trace hp hp1 hq hs w).1 ⟨x, hx', h⟩
    refine ⟨hw, ?_, hi⟩
    rw [coord hx' h, ← slitArcRe_one]
    exact slitArcRe_strictAnti hp hx' ⟨hp1.le, le_rfl⟩ hx.2
  · rintro ⟨hw, hl, hi⟩
    obtain ⟨x, hx, h⟩ := (slitMap_bank_trace hp hp1 hq hs w).2 ⟨hw, hl.le, hi⟩
    refine ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩, h⟩
    rintro rfl
    rw [coord hx h, slitArcRe_one] at hl
    exact lt_irrefl _ hl

/-- Figure 2 for the paper's parameter. The joined banks are exactly the closed unit-circle
arc around 1 cut out by the vertical line with real coordinate 7/9. -/
theorem figure2_arc {q : ℂ → ℂ} (hq : IsSlitMap (1/2) q) (w : ℂ) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ x ∈ Icc (1/2 : ℝ) 1,
      Tendsto q (𝓝[slitBank (1/2) s] (x : ℂ)) (𝓝 w)) ↔
    ‖w‖ = 1 ∧ 7/9 ≤ w.re := by
  have hr : 2 * slitR (1/2) - 1 = 7/9 := by norm_num [slitR]
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨hw, hl, _⟩ := (slitMap_bank_trace (by norm_num) (by norm_num) hq hs w).mp h
    exact ⟨hw, hr ▸ hl⟩
  · rintro ⟨hw, hl⟩
    rw [← hr] at hl
    rcases le_total 0 w.im with hi | hi
    · exact ⟨1, Or.inl rfl, (slitMap_bank_trace (by norm_num) (by norm_num) hq (Or.inl rfl) w).2
        ⟨hw, hl, by simpa using hi⟩⟩
    · exact ⟨-1, Or.inr rfl, (slitMap_bank_trace (by norm_num) (by norm_num) hq (Or.inr rfl) w).2
        ⟨hw, hl, by simpa using hi⟩⟩

/-- info: 'Goodman.slitMap_bank_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitMap_bank_limit

/-- info: 'Goodman.slitMap_tip_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitMap_tip_limit

/-- info: 'Goodman.slitMap_bank_trace_Ico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitMap_bank_trace_Ico

/-- info: 'Goodman.figure2_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms figure2_arc

/-- info: 'Goodman.figure3_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms figure3_segment

end Goodman
