-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Geometry

noncomputable section
open Set Filter Topology

namespace Goodman

private def sphereInv (x : Sphere) : Sphere := x.elim (0 : ℂ) fromRecip

private theorem continuous_fromRecip : Continuous fromRecip := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    apply continuousAt_iff_punctured_nhds.mpr
    have h : Tendsto (fun t : ℂ => (t⁻¹ : ℂ)) (𝓝[≠] 0) (coclosedCompact ℂ) := by
      simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_nhdsNE_zero (α := ℂ))
    rw [show fromRecip 0 = OnePoint.infty by simp [fromRecip]]
    apply (OnePoint.tendsto_coe_infty.comp h).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [Function.comp_apply, fromRecip, show t ≠ 0 from ht]
  · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with t ht
    simp [Function.comp_apply, fromRecip, ht]

private theorem continuous_sphereInv : Continuous sphereInv := by
  apply (OnePoint.continuous_iff _).2
  refine ⟨?_, continuous_fromRecip⟩
  have h : Tendsto (fun z : ℂ => z⁻¹) (coclosedCompact ℂ) (𝓝 0) := by
    simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded (α := ℂ))
  apply (OnePoint.continuous_coe.continuousAt.tendsto.comp h).congr'
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_coclosedCompact_of_isClosed isClosed_singleton] with z hz
  simp [Function.comp_apply, sphereInv, fromRecip, show z ≠ 0 from hz]

private theorem sphereInv_involutive : Function.Involutive sphereInv := by
  intro x
  induction x using OnePoint.rec with
  | infty => simp [sphereInv, fromRecip]
  | coe z =>
    by_cases hz : z = 0 <;> simp [sphereInv, fromRecip, hz]

private def reciprocalHomeomorph : Sphere ≃ₜ Sphere where
  toFun := sphereInv
  invFun := sphereInv
  left_inv := sphereInv_involutive
  right_inv := sphereInv_involutive
  continuous_toFun := continuous_sphereInv
  continuous_invFun := continuous_sphereInv

/-- Move the omitted point to infinity. At a finite omitted point the map is
translation by `-a` followed by reciprocal inversion. -/
def moveOmitted : Sphere → Sphere ≃ₜ Sphere :=
  OnePoint.rec (Homeomorph.refl _) fun a : ℂ =>
    (Homeomorph.subRight a).onePointCongr.trans reciprocalHomeomorph

@[simp] theorem moveOmitted_self (p : Sphere) : moveOmitted p p = OnePoint.infty := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe a =>
    change fromRecip (a - a) = _
    simp [fromRecip]

def omittedCoord (p x : Sphere) : ℂ := finitePart (moveOmitted p x)

def omittedParam (p : Sphere) (z : ℂ) : Sphere := (moveOmitted p).symm (z : Sphere)

theorem omittedCoord_param (p : Sphere) (z : ℂ) : omittedCoord p (omittedParam p z) = z := by
  simp only [omittedCoord, omittedParam, Homeomorph.apply_symm_apply]
  rfl

theorem omittedParam_coord {p x : Sphere} (hx : x ≠ p) :
    omittedParam p (omittedCoord p x) = x := by
  have h : moveOmitted p x ≠ OnePoint.infty := fun he =>
    hx ((moveOmitted p).injective (he.trans (moveOmitted_self p).symm))
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp h
  apply (moveOmitted p).injective
  simp only [omittedParam, Homeomorph.apply_symm_apply, omittedCoord, ← hz]
  rfl

theorem omittedParam_range (p : Sphere) : range (omittedParam p) = {p}ᶜ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩ he
    change omittedParam p z = p at he
    have h := congrArg (moveOmitted p) he
    simp [omittedParam] at h
  · intro hx
    exact ⟨_, omittedParam_coord hx⟩

theorem isOpenEmbedding_omittedParam (p : Sphere) : IsOpenEmbedding (omittedParam p) :=
  (moveOmitted p).symm.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe

/-- The complement of any point has one affine coordinate covering it. -/
def omittedChart (p : Sphere) : ({p}ᶜ : Set Sphere) ≃ₜ ℂ :=
  ((isOpenEmbedding_omittedParam p).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (omittedParam_range p))).symm

theorem omittedChart_apply (p : Sphere) (x : ({p}ᶜ : Set Sphere)) :
    omittedChart p x = omittedCoord p x := by
  apply (omittedChart p).symm.injective
  apply Subtype.ext
  change _ = omittedParam p (omittedCoord p x)
  rw [omittedParam_coord x.property]
  exact congrArg Subtype.val ((omittedChart p).symm_apply_apply x)

/-- With infinity omitted, use the usual affine embedding and coordinate. -/
@[simp] theorem omittedParam_of_omitted_infty (z : ℂ) :
    omittedParam OnePoint.infty z = (z : Sphere) := rfl

@[simp] theorem omittedCoord_of_omitted_infty (x : Sphere) :
    omittedCoord OnePoint.infty x = finitePart x := rfl

@[simp] theorem omittedCoord_finite (a z : ℂ) :
    omittedCoord (a : Sphere) (z : Sphere) = (z - a)⁻¹ := by
  change finitePart (fromRecip (z - a)) = _
  by_cases h : z - a = 0 <;> simp [fromRecip, h] <;> rfl

@[simp] theorem omittedCoord_infty (a : ℂ) :
    omittedCoord (a : Sphere) OnePoint.infty = 0 := rfl

@[simp] theorem omittedParam_finite (a t : ℂ) : omittedParam (a : Sphere) t =
    if t = 0 then OnePoint.infty else ((t⁻¹ + a : ℂ) : Sphere) := by
  change OnePoint.map _ (fromRecip t) = _
  by_cases ht : t = 0 <;> simp [fromRecip, ht]

/-- The reciprocal coordinate at infinity gives the germ `t / (1 - a*t)`. -/
theorem omittedCoord_holomorphic (p : Sphere) :
    HolomorphicFromSphereOn (omittedCoord p) {p}ᶜ := by
  induction p using OnePoint.rec with
  | infty =>
    refine ⟨fun _ _ => analyticAt_id, fun h => False.elim (h rfl)⟩
  | coe a =>
    constructor
    · intro z hz
      simp only [omittedCoord_finite]
      apply (analyticAt_id.sub analyticAt_const).inv
      exact sub_ne_zero.mpr fun he => hz (congrArg OnePoint.some he)
    · intro _
      have hD : AnalyticAt ℂ (fun t : ℂ => 1 - a*t) 0 :=
        analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
      apply (analyticAt_id.div hD (by simp)).congr
      apply Filter.Eventually.of_forall
      intro t
      change t / (1 - a*t) = omittedCoord (a : Sphere) (fromRecip t)
      by_cases h : t = 0
      · simp [h, fromRecip]
      · simp only [fromRecip, ite_eq_right h, omittedCoord_finite]
        rw [show t⁻¹ - a = (1 - a*t) / t by field_simp, inv_div]

/-- In the pole germ the spherical parametrization has reciprocal coordinate
`t / (1 + a*t)`; away from zero it has affine coordinate `t⁻¹ + a`. -/
theorem omittedParam_comp_holomorphic (p : Sphere) {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) : SphereHolomorphicOn (omittedParam p ∘ f) Ω := by
  intro x hx
  induction p using OnePoint.rec with
  | infty => exact ⟨f, hf x hx, Or.inl (.of_forall fun _ => rfl)⟩
  | coe a =>
    by_cases h : f x = 0
    · have hD : AnalyticAt ℂ (fun t => 1 + a * f t) x :=
        analyticAt_const.add (analyticAt_const.mul (hf x hx))
      have hn : 1 + a * f x ≠ 0 := by simp [h]
      refine ⟨fun t => f t / (1 + a * f t), (hf x hx).div hD hn, Or.inr ?_⟩
      filter_upwards [hD.continuousAt.eventually_ne hn] with t ht
      change omittedParam (a : Sphere) (f t) = fromRecip _
      by_cases hz : f t = 0
      · simp [hz, fromRecip]
      · simp only [omittedParam_finite, ite_eq_right hz, fromRecip, ite_eq_right (div_ne_zero hz ht),
          OnePoint.coe_eq_coe, inv_div]
        field_simp
    · refine ⟨fun t => (f t)⁻¹ + a, ((hf x hx).inv h).add analyticAt_const, Or.inl ?_⟩
      filter_upwards [(hf x hx).continuousAt.eventually_ne h] with t ht
      simp [Function.comp_apply, ht]

end Goodman
