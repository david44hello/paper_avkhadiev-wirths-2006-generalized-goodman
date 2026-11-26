-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Fejer
import Goodman.Lagrange
import Goodman.DiskDerivative
import Goodman.Centered
import Goodman.Deficit
import Goodman.Slit
import Goodman.Product

noncomputable section
open Set Metric Filter
open scoped Topology

namespace Goodman

private theorem zero_mem_unit : (0 : ℂ) ∈ disk := by simp [disk]

private theorem analytic_dslope_disk {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f disk) :
    AnalyticOnNhd ℂ (dslope f 0) disk :=
  ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds zero_mem_unit)).2
    hf.differentiableOn).analyticOnNhd isOpen_ball

/-- Marx--Strohhäcker followed by Schwarz, including the removable value at zero. -/
theorem convex_reciprocal_weight (hMS : MarxStrohhacker) {s : ℂ → ℂ}
    (hs : IsS s) (hc : Convex ℝ (s '' disk)) :
    ∃ v, IsWeight v ∧ EqOn (fun z => 1 / dslope s 0 z) (fun z => 1 + z * v z) disk := by
  let u := dslope s 0
  have hu : AnalyticOnNhd ℂ u disk := analytic_dslope_disk hs.1
  have hu0 : u 0 = 1 := (dslope_same ..).trans hs.2.2.2
  have hfac (z : ℂ) : z * u z = s z := by simpa [u, hs.2.2.1] using sub_smul_dslope s 0 z
  have hre (z : ℂ) (hz : z ∈ disk) : 1 / 2 < (u z).re := by
    rcases eq_or_ne z 0 with rfl | hn
    · rw [hu0]; norm_num
    · have he : s z / z = u z := by rw [← hfac, mul_div_cancel_left₀ _ hn]
      simpa only [he] using hMS s hs hc z hz hn
  have hne (z : ℂ) (hz : z ∈ disk) : u z ≠ 0 := by
    intro h
    have := hre z hz
    norm_num [h] at this
  let q (z : ℂ) := 1 / u z - 1
  have hq : AnalyticOnNhd ℂ q disk := fun z hz =>
    (analyticAt_const.fun_div (hu z hz) (hne z hz)).fun_sub analyticAt_const
  have hq0 : q 0 = 0 := by simp [q, hu0]
  have hmap : MapsTo q (ball 0 1) (closedBall (q 0) 1) := by
    intro z hz
    rw [hq0, mem_closedBall_zero_iff]
    have he : q z = (1 - u z) / u z := by
      dsimp [q]
      field_simp [hne z hz]
    rw [he, norm_div, div_le_one (norm_pos_iff.mpr (hne z hz))]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [hre z hz]
  refine ⟨dslope q 0, ⟨analytic_dslope_disk hq, fun z hz => ?_⟩, fun z _ => ?_⟩
  · simpa using Complex.norm_dslope_le_div_of_mapsTo_ball hq.differentiableOn hmap hz
  · have h := sub_smul_dslope q 0 z
    simp only [sub_zero, hq0, smul_eq_mul] at h
    change 1 / u z = 1 + z * dslope q 0 z
    rw [h]
    dsimp [q]
    ring

private theorem coeff_monomial_shift {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (m d : ℕ) :
    coeff m (fun z => z^d * f z) = if d ≤ m then coeff (m-d) f else 0 := by
  have hm (i : ℕ) : coeff i (fun z : ℂ => z^d) = if i = d then 1 else 0 := by
    rw [coeff, iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst i; simp [Nat.cast_ne_zero.mpr d.factorial_ne_zero]
    · simp
  rw [coeff_mul (f := fun z => z^d) (analyticAt_id.fun_pow d) hf]
  simp [hm, ite_mul, Finset.sum_ite_eq']

/-- The upper binomial endpoint has too high a source degree. Indexing the
surviving terms by their derivative order avoids truncated subtraction in D. -/
theorem convex_binomial_coeff {H v : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (hv : AnalyticAt ℂ v 0) (m : ℕ) :
    coeff m (fun z => deriv H z * (1 + z * v z)^(m+1)) =
      ∑ i ∈ Finset.range (m+1), ((m+1).choose (i+1) : ℂ) *
        coeff i (fun z => deriv H z * v z ^ (m-i)) := by
  let T (j : ℕ) (z : ℂ) := ((m+1).choose j : ℂ) *
    (z^(m+1-j) * (deriv H z * v z^(m+1-j)))
  have hT (j : ℕ) : AnalyticAt ℂ (T j) 0 := analyticAt_const.fun_mul
    ((analyticAt_id.fun_pow _).fun_mul (hH.deriv.fun_mul (hv.fun_pow _)))
  have he : (fun z => deriv H z * (1 + z * v z)^(m+1)) =
      fun z => ∑ j ∈ Finset.range (m+1+1), T j z := by
    funext z
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [T, one_pow, one_mul, mul_pow]
    ring
  have hsum : coeff m (fun z => ∑ j ∈ Finset.range (m+1+1), T j z) =
      ∑ j ∈ Finset.range (m+1+1), coeff m (T j) := by
    simp only [coeff, iteratedDeriv_fun_sum (fun j _ => (hT j).contDiffAt), Finset.sum_div]
  rw [he, hsum, Finset.sum_range_succ']
  have ht (j : ℕ) : coeff m (T j) = ((m+1).choose j : ℂ) *
      (if m+1-j ≤ m then coeff (m-(m+1-j)) (fun z => deriv H z * v z ^ (m+1-j)) else 0) := by
    dsimp only [T]
    rw [coeff_fun_const_mul, coeff_monomial_shift (hH.deriv.fun_mul (hv.fun_pow _))]
  rw [ht 0]
  simp only [Nat.sub_zero, Nat.not_succ_le_self, ite_false, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [ht (i+1), Nat.add_sub_add_right, ite_eq_left (Nat.sub_le ..), show m - (m-i) = i by omega]

/-- Bound the numerator in Lagrange's formula using powers of the actual
disk weight supplied by Marx--Strohhäcker. -/
theorem convex_lagrange_numerator_bound (hMS : MarxStrohhacker) {s H : ℂ → ℂ}
    (hs : IsS s) (hc : Convex ℝ (s '' disk)) (hH : AnalyticAt ℂ H 0) (h0 : H 0 = 0)
    {p : ℝ} (hb : ∀ k, 1 ≤ k → ∀ W, IsWeight W →
      ‖coeff k (fun z => H z * W z)‖ ≤ A p k) (m : ℕ) :
    ‖coeff m (fun z => deriv H z * (1 / dslope s 0 z)^(m+1))‖ ≤
      (m+1 : ℕ) * D p 1 (m+1) := by
  obtain ⟨v, hv, he⟩ := convex_reciprocal_weight hMS hs hc
  have hg : (fun z => deriv H z * (1 / dslope s 0 z)^(m+1)) =ᶠ[𝓝 0]
      fun z => deriv H z * (1 + z * v z)^(m+1) := by
    filter_upwards [isOpen_ball.mem_nhds zero_mem_unit] with z hz
    exact congrArg (fun u : ℂ => deriv H z * u^(m+1)) (he hz)
  rw [coeff_congr_of_eventuallyEq hg, convex_binomial_coeff hH (hv.1 0 zero_mem_unit)]
  apply (norm_sum_le _ _).trans
  unfold D
  simp only [Nat.add_sub_cancel, one_pow, mul_one, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hw : IsWeight (fun z => v z ^ (m-i)) :=
    ⟨fun z hz => (hv.1 z hz).fun_pow _, fun z hz => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hv.2 z hz)⟩
  have hd := fejer_derivative_bound hH h0 (k := i+1) (by omega) (hb _ (by omega)) hw
  simp only [Nat.add_sub_cancel] at hd
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ ((m+1).choose (i+1) : ℝ) * (((i+1 : ℕ) : ℝ) * A p (i+1)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← Nat.cast_mul, ← Nat.add_one_mul_choose_eq]
      push_cast
      ring

/-- Rotate a centered planar parametrization so its derivative is positive. -/
private theorem positive_source_chart (hR : PlanarRiemannMapping) {Ω : Set ℂ}
    (hΩ : IsSource Ω) {x : ℂ} (hx : x ∈ Ω) :
    ∃ φ : ℂ → ℂ, Bihol disk Ω φ ∧ φ 0 = x ∧
      0 < ‖deriv φ 0‖ ∧ deriv φ 0 = (‖deriv φ 0‖ : ℂ) := by
  obtain ⟨f, hB, hf0⟩ := exists_centered_planar_bihol hR hΩ hx
  obtain ⟨hf, χ, hχ, hm, hmi, hl, hr⟩ := hB
  have hid : χ ∘ f =ᶠ[𝓝 0] id := by
    filter_upwards [isOpen_ball.mem_nhds zero_mem_unit] with z hz using hl hz
  let b := deriv f 0
  have hb : b ≠ 0 := by
    have h : deriv χ (f 0) * deriv f 0 = 1 := by
      rw [← deriv_comp 0 (hχ _ (hm zero_mem_unit)).differentiableAt
        (hf _ zero_mem_unit).differentiableAt, hid.deriv_eq, deriv_id]
    intro he
    change deriv f 0 = 0 at he
    simp [he] at h
  let a : ℂ := (‖b‖ : ℂ) / b
  have ha : ‖a‖ = 1 := by simp [a, norm_ne_zero_iff.mpr hb]
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (ha.trans_ne one_ne_zero)
  have maps {c : ℂ} (hc : ‖c‖ = 1) : MapsTo (fun z => c*z) disk disk := by
    intro z hz
    simpa [disk, mem_ball_zero_iff, norm_mul, hc] using hz
  have ma := maps ha
  have mai := maps (c := a⁻¹) (by simp [ha])
  let φ (z : ℂ) := f (a*z)
  have hd : deriv φ 0 = (‖b‖ : ℂ) := by
    dsimp only [φ]
    rw [deriv_comp_mul_left, mul_zero]
    change a • b = _
    simp [a, smul_eq_mul, hb]
  refine ⟨φ, ⟨fun z hz => (hf _ (ma hz)).comp (analyticAt_const.fun_mul analyticAt_id),
    fun y => a⁻¹ * χ y, fun y hy => analyticAt_const.fun_mul (hχ y hy),
    hm.comp ma, mai.comp hmi, ?_, ?_⟩, by simpa [φ] using hf0, ?_, ?_⟩
  · intro z hz
    change a⁻¹ * χ (f (a*z)) = z
    rw [hl (ma hz), inv_mul_cancel_left₀ ha0]
  · intro y hy
    change f (a * (a⁻¹ * χ y)) = y
    rw [mul_inv_cancel_left₀ ha0, hr hy]
  · rw [hd, Complex.norm_of_nonneg (norm_nonneg _)]
    exact norm_pos_iff.mpr hb
  · rw [hd, Complex.norm_of_nonneg (norm_nonneg _)]

private theorem normalized_source_convex {φ : ℂ → ℂ} {Ω : Set ℂ} (hB : Bihol disk Ω φ)
    (hc : Convex ℝ Ω) (x : ℂ) {r : ℂ} (hr : r ≠ 0) :
    Convex ℝ ((fun z => (φ z - x) / r) '' disk) := by
  obtain ⟨_, χ, _, hm, hi, _, hright⟩ := hB
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ a b ha hb hab
  let t := a • φ y + b • φ z
  have ht : t ∈ Ω := hc (hm hy) (hm hz) ha hb hab
  refine ⟨χ t, hi ht, ?_⟩
  dsimp only
  rw [hright ht]
  simp only [t, Complex.real_smul]
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  field_simp [hr]
  linear_combination x * hab'

/-- Lagrange inversion turns the numerator estimate into a bound for the
Taylor coefficient in the normalized affine source coordinate. -/
theorem convex_composition_bound (hMS : MarxStrohhacker) {s H g : ℂ → ℂ}
    (hs : IsS s) (hc : Convex ℝ (s '' disk)) (hg : AnalyticAt ℂ g 0)
    (he : H =ᶠ[𝓝 0] g ∘ s) (h0 : H 0 = 0) {p : ℝ}
    (hb : ∀ k, 1 ≤ k → ∀ W, IsWeight W → ‖coeff k (fun z => H z * W z)‖ ≤ A p k)
    {n : ℕ} (hn : 1 ≤ n) : ‖coeff n g‖ ≤ D p 1 n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hH : AnalyticAt ℂ H 0 :=
    (hg.comp_of_eq (hs.1 0 zero_mem_unit) hs.2.2.1).congr he.symm
  have h := convex_lagrange_numerator_bound hMS hs hc hH h0 hb m
  have hlag := lagrange_inversion_coeff (hs.1 0 zero_mem_unit) hs.2.2.1 hs.2.2.2 hg he hn
  rw [Nat.succ_sub_one] at hlag
  rw [← hlag, norm_mul, Complex.norm_natCast] at h
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (m+1 : ℕ))).mp h

/-- Theorem 3(b) for a convex source and a spherical target, obtained from the
centered weighted estimate and the two classical geometric inputs. -/
theorem convexDerivativeBound_of_centeredClaim (hC : CenteredClaim) (hMS : MarxStrohhacker)
    (hR : PlanarRiemannMapping) : ConvexDerivativeBound := by
  intro Ω U x w hΩ hc hx hU G hG hm hw n hn
  obtain ⟨φ, hφ, hφ0, hpos, hder⟩ := positive_source_chart hR hΩ hx
  let r := radius (planeDomain Ω) x
  let t := radius U w
  have hr : r = ‖deriv φ 0‖ := by
    simpa only [hφ0] using radius_planeDomain_of_bihol hφ
  have hr0 : 0 < r := hr ▸ hpos
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hd : deriv φ 0 = (r : ℂ) := hr ▸ hder
  have ht : 0 ≤ t := by unfold t radius; split <;> positivity
  let s (z : ℂ) := (φ z - x) / (r : ℂ)
  let g (z : ℂ) := (finitePart (G (x + (r : ℂ) * z)) - w) / (t : ℂ)
  let H (z : ℂ) := (finitePart (G (φ z)) - w) / (t : ℂ)
  obtain ⟨χ, _, _, _, hl, _⟩ := hφ.2
  have hs : IsS s := by
    refine ⟨fun z hz => ((hφ.1 z hz).sub analyticAt_const).div_const, ?_, ?_, ?_⟩
    · intro y hy z hz he
      exact hl.injOn hy hz (sub_left_inj.mp ((div_left_inj' hrne).mp he))
    · simp [s, hφ0]
    · dsimp only [s]
      rw [deriv_div_const, deriv_sub_const, hd, div_self hrne]
  have hgx := (hG.affine_germ hx (hw ▸ OnePoint.coe_ne_infty w)).1
  have ha : AnalyticAt ℂ (fun z : ℂ => x + (r : ℂ)*z) 0 := by fun_prop
  have hg : AnalyticAt ℂ g 0 :=
    ((hgx.comp_of_eq ha (by simp)).sub analyticAt_const).div_const
  have he : H =ᶠ[𝓝 0] g ∘ s := Eventually.of_forall fun z => by
    simp [H, g, s, Function.comp_apply, mul_div_cancel₀ _ hrne]
  have h0 : H 0 = 0 := by
    simp only [H, hφ0, hw, show finitePart (w : Sphere) = w from rfl, sub_self, zero_div]
  have hb (k : ℕ) (hk : 1 ≤ k) (W : ℂ → ℂ) (hW : IsWeight W) :
      ‖coeff k (fun z => H z * W z)‖ ≤ A (poleParam U w) k := by
    simpa only [H, t, mul_comm] using hC Ω U x w hΩ hx hU G hG hm hw φ hφ hφ0 hd W hW k hk
  rw [derivativeRatio_eq_affine_coeff G x w hr0.le ht n (by omega)]
  exact convex_composition_bound hMS hs (normalized_source_convex hφ hc x hrne) hg he h0 hb (by omega)

#print axioms convexDerivativeBound_of_centeredClaim

/-- The printed convex derivative bound with the centered lemma discharged. -/
theorem convexDerivativeBound (hRob : Robertson) (hMS : MarxStrohhacker)
    (hR : PlanarRiemannMapping) : ConvexDerivativeBound := by
  have product := product_of_robertson hRob
  have weighted := MainReduction.weighted_of_transfer_slit_deficit transfer slit_proved
    (deficit_of_product product)
  exact convexDerivativeBound_of_centeredClaim
    (centeredClaim weighted transfer product (riemannMapping_of_planarRiemannMapping hR)) hMS hR

#print axioms convexDerivativeBound

end Goodman
