-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.MobiusSphere
public import Challenge.JoukowskiAffine
public import Challenge.SegmentScale
public import Challenge.SlitArcCoordinate
public import Challenge.SlitScale
public import Goodman.SharpModels
public import Goodman.PlanarUniformization
public import Goodman.CoefficientClaims

@[expose] public section

section

noncomputable section
namespace Goodman

theorem aligned_of_saturated_sum {ι : Type*} (s : Finset ι) (w B : ι → ℝ) (a : ι → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, ‖a i‖ ≤ B i)
    {j : ι} (hj : j ∈ s) (hwj : 0 < w j) (haj : a j = 1) (hbj : B j = 1)
    (sat : ‖∑ i ∈ s, (w i : ℂ) * a i‖ = ∑ i ∈ s, w i * B i) :
    ∀ i ∈ s, 0 < w i → a i = (B i : ℂ) := by sorry

end Goodman
end
end

section

open Metric Filter
open scoped Topology
namespace Goodman

theorem caratheodory_disk_coefficient {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g disk)
    (hpos : ∀ z ∈ disk, 0 ≤ (g z).re) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n g‖ ≤ 2 * (g 0).re := by sorry

end Goodman
end

section

open Filter
open scoped Topology
namespace Goodman

theorem coeff_comp_finite {F q : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hq : AnalyticAt ℂ q 0)
    (hq0 : q 0 = 0) (n : ℕ) :
    coeff n (F ∘ q) = ∑ k ∈ Finset.range (n + 1), coeff k F * coeff n (fun z => q z ^ k) := by sorry

end Goodman
end

section

noncomputable section
open Filter
open scoped Topology
namespace Goodman

theorem A_at_one (n : ℕ) : A 1 n = n := by sorry

theorem A_first (p : ℝ) : A p 1 = 1 := by sorry

theorem A_positive {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) : 0 < A p n := by sorry

theorem A_closed {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    A p n = (1 - p^(2*n)) / ((1 - p^2) * p^(n-1)) := by sorry

theorem A_succ_binomial {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (j : ℕ) :
    (1-p^2) * A p (j+1) = (1/p)^j - p^2*p^j := by sorry

theorem D_closed {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (r : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    D p r n = ((r+1/p)^(n-1) - p^2*(r+p)^(n-1)) / (1-p^2) := by sorry

theorem A_tendsto_one (n : ℕ) : Tendsto (fun p : ℝ => A p n) (𝓝 1) (𝓝 (n : ℝ)) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem extremal_hasSum {p : ℝ} (hp : p ≠ 0) {z : ℂ}
    (h₁ : ‖(p : ℂ) * z‖ < 1) (h₂ : ‖z / p‖ < 1) :
    HasSum (fun k ↦ z ^ k * (A p k : ℂ)) (finitePart (extremal p z)) := by sorry

theorem coeff_extremal_scaled {p : ℝ} (hp : p ≠ 0) (a : ℂ) (n : ℕ) :
    coeff n (fun z ↦ finitePart (extremal p (a * z))) = a ^ n * (A p n : ℂ) := by sorry

theorem coeff_extremal_of_ne_zero {p : ℝ} (hp : p ≠ 0) (n : ℕ) :
    coeff n (finitePart ∘ extremal p) = (A p n : ℂ) := by sorry

theorem isM_extremal {p : ℝ} (hp : 0 < p) (hp' : p < 1) : IsM p (extremal p) := by sorry

theorem finitePart_extremal_one :
    finitePart ∘ extremal 1 = fun z : ℂ ↦ z / (1 - z) ^ 2 := by sorry

end Goodman
end
end

section

noncomputable section
open Complex Filter MeasureTheory Metric Real Set
open scoped Topology ComplexConjugate
namespace Goodman
local notation "𝕋" => AddCircle (2 * π)
local instance instFactLtRealOfNatHMulPi_goodman : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
local notation "σ" => (AddCircle.haarAddCircle (T := 2 * π))
local notation "ζ" => (fun θ : 𝕋 => (AddCircle.toCircle θ : ℂ))

theorem transfer_hardy_boundary {f : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hneg : ∀ i : ℤ, i < 0 → fourierCoeff f i = 0) :
    ∃ E : ℂ → ℂ, IsWeight E ∧ (∀ n : ℕ, coeff n E = fourierCoeff f n) ∧
      (∀ᵐ x ∂σ, Tendsto (fun r : ℝ => E ((r : ℂ) * ζ x)) (𝓝[<] 1) (𝓝 (f x))) ∧
      Tendsto (fun r : ℝ => ∫ x, ‖E ((r : ℂ) * ζ x) - f x‖^2 ∂σ) (𝓝[<] 1) (𝓝 0) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem reversed_polynomial_boundary (c : ℕ → ℂ) (n : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    (∑ j ∈ Finset.range (n+1), c j * w^(n-j)) =
      w^n * ∑ j ∈ Finset.range (n+1), c j * (w⁻¹)^j := by sorry

theorem reversed_polynomial_weight (c : ℕ → ℂ) (n : ℕ)
    (hb : ∀ t : ℂ, ‖t‖ = 1 → ‖∑ j ∈ Finset.range (n+1), c j * t^j‖ ≤ 1) :
    IsWeight (fun w : ℂ => ∑ j ∈ Finset.range (n+1), c j * w^(n-j)) := by sorry

end Goodman
end
end

section

noncomputable section
open Set
namespace Goodman

theorem exists_isSlitMap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ q, IsSlitMap p q := by sorry

end Goodman
end
end

section

noncomputable section
namespace Goodman

theorem norm_sum_le_first_deficit {n : ℕ} (hn : 1 ≤ n) (d : ℕ → ℂ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (h0 : d 0 = 0) (hd : ∀ k, 1 ≤ k → ‖d k‖ ≤ (k : ℝ)) :
    ‖∑ k ∈ Finset.range (n+1), d k * (w k : ℂ)‖ ≤
      (∑ k ∈ Finset.range (n+1), (k : ℝ) * w k) - w 1 * (1 - ‖d 1‖) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem exists_normalized_square_factor {F : ℂ → ℂ} (hF : IsS F) :
    ∃ M : ℂ → ℂ, AnalyticOnNhd ℂ M disk ∧ M 0 = 1 ∧
      (∀ z ∈ disk, M z ≠ 0) ∧ ∀ z ∈ disk, F z = z * M z ^ 2 := by sorry

theorem exists_odd_square_factor {F : ℂ → ℂ} (hF : IsS F) :
    ∃ M : ℂ → ℂ, AnalyticOnNhd ℂ M disk ∧ (∀ z ∈ disk, F z = z * M z ^ 2) ∧
      IsS (fun z => z * M (z ^ 2)) ∧
      (∀ z ∈ disk, (-z) * M ((-z) ^ 2) = -(z * M (z ^ 2))) ∧
      ∀ z ∈ disk, (z * M (z ^ 2)) ^ 2 = F (z ^ 2) := by sorry

theorem coeff_odd_square_pullback (j : ℕ) {M : ℂ → ℂ} (hM : AnalyticOnNhd ℂ M disk) :
    coeff (2*j+1) (fun z => z * M (z ^ 2)) = coeff j M := by sorry

open scoped Polynomial
open scoped ComplexConjugate

theorem product_of_robertson (hR : Robertson) : ProductClaim := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem IsSchwarz.norm_deriv_eq_one_iff_isRotation {h : ℂ → ℂ} (hh : IsSchwarz h) :
    ‖deriv h 0‖ = 1 ↔ IsRotation h := by sorry

theorem coeff_comp_mul_left (g : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    coeff n (fun z => g (a * z)) = a ^ n * coeff n g := by sorry

theorem IsM.finite_germ_zero {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f) :
    AnalyticAt ℂ (finitePart ∘ f) 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), f z = (finitePart (f z) : Sphere) := by sorry

theorem IsM.hasDerivAt_zero {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f) :
    HasDerivAt (finitePart ∘ f) 1 0 := by sorry

theorem IsM.finite_comp_of_norm_lt {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f)
    (hp : 0 < p) (hp1 : p < 1) {h : ℂ → ℂ} (hh : IsSchwarz h) {z : ℂ} (hz : ‖z‖ < p) :
    f (h z) ≠ OnePoint.infty ∧ AnalyticAt ℂ (fun w => finitePart (f (h w))) z := by sorry

theorem IsM.coeff_one_comp {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f)
    {h : ℂ → ℂ} (hh : IsSchwarz h) :
    coeff 1 (fun z => finitePart (f (h z))) = deriv h 0 := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem slitR_pos {p : ℝ} (hp : 0 < p) : 0 < slitR p := by sorry

theorem slit_majorant_hasSum {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum
      (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (finitePart (extremal p z)) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric Complex
open scoped Topology
namespace Goodman

theorem transfer_moment {e h : ℂ → ℂ} (he : AnalyticAt ℂ e 0)
    (hh : AnalyticAt ℂ h 0) (hz : h 0 = 0) (n j : ℕ) (hnj : n ≤ j) :
    coeff n (fun z => e z * h z ^ j) = if j = n then e 0 * deriv h 0 ^ n else 0 := by sorry

theorem transfer_coeff_composition {e h g : ℂ → ℂ} (he : AnalyticAt ℂ e 0)
    (hh : AnalyticAt ℂ h 0) (hz : h 0 = 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => e z * g (h z)) =
      ∑ j ∈ Finset.range (n+1), coeff j g * coeff n (fun z => e z * h z ^ j) := by sorry

open scoped ComplexConjugate

theorem transfer_coeff_product {E g : ℂ → ℂ} (hE : AnalyticAt ℂ E 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => E z * g z) =
      ∑ j ∈ Finset.range (n+1), coeff j g * coeff (n-j) E := by sorry

end Goodman
end
end

section

open Filter Metric
open scoped Topology
namespace Goodman

theorem szapiel_coeff_eq {h : ℂ → ℂ} (hh : IsSchwarz h) (t : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (fun z => (1 + t * h z) / (1 - t * h z)) =
      2 * ∑ j ∈ Finset.range (n + 1), coeff n (fun z => h z ^ j) * t ^ j := by sorry

theorem szapiel_moment_bound {h : ℂ → ℂ} (hh : IsSchwarz h) {t : ℂ} (ht : ‖t‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖∑ j ∈ Finset.range (n + 1), coeff n (fun z => h z ^ j) * t ^ j‖ ≤ 1 := by sorry

end Goodman
end

section

noncomputable section
open Filter Metric
open scoped Topology Polynomial
namespace Goodman

def productTaylorPoly (M : ℂ → ℂ) (k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range k, Polynomial.monomial j (coeff j M)

theorem productTaylorPoly_eval (M : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (productTaylorPoly M k).eval z = ∑ j ∈ Finset.range k, coeff j M * z ^ j := by sorry

theorem product_truncation_identity {F M E : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hM : AnalyticAt ℂ M 0) (hE : AnalyticAt ℂ E 0)
    (hfac : ∀ z ∈ disk, F z = z * M z ^ 2) :
    let P := productTaylorPoly M k
    coeff k (fun z => F z * E z) = coeff (k-1) (fun z => M z ^ 2 * E z) ∧
    coeff (k-1) (fun z => M z ^ 2 * E z) =
      coeff (k-1) (fun z => (P.eval z * E z) * P.eval z) := by sorry

def hardyTwoNorm (f : ℂ → ℂ) : ℝ := √(∑' j : ℕ, ‖coeff j f‖ ^ 2)

theorem product_truncation_parseval (M : ℂ → ℂ) (k : ℕ) :
    hardyTwoNorm (productTaylorPoly M k).eval ^ 2 =
      ∑ j ∈ Finset.range k, ‖coeff j M‖ ^ 2 := by sorry

theorem hardyTwo_weight_contraction {f E : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hs : Summable (fun j => ‖coeff j f‖ ^ 2)) (hE : IsWeight E) :
    Summable (fun j => ‖coeff j (fun z => f z * E z)‖ ^ 2) ∧
      hardyTwoNorm (fun z => f z * E z) ≤ hardyTwoNorm f := by sorry

theorem coeff_product_finite_cauchy_schwarz (n : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ‖coeff n (fun z => f z * g z)‖ ≤
      √(∑ i ∈ Finset.range (n+1), ‖coeff i f‖ ^ 2) *
      √(∑ i ∈ Finset.range (n+1), ‖coeff i g‖ ^ 2) := by sorry

theorem product_hardy_cauchy_schwarz (M : ℂ → ℂ) (k : ℕ) {E : ℂ → ℂ} (hE : IsWeight E) :
    let P := productTaylorPoly M k
    ‖coeff (k-1) (fun z => (P.eval z * E z) * P.eval z)‖ ≤
      hardyTwoNorm (fun z => P.eval z * E z) * hardyTwoNorm P.eval := by sorry

theorem product_hardy_contraction (M : ℂ → ℂ) (k : ℕ) {E : ℂ → ℂ} (hE : IsWeight E) :
    let P := productTaylorPoly M k
    hardyTwoNorm (fun z => P.eval z * E z) ≤ hardyTwoNorm P.eval := by sorry

theorem product_hardy_robertson_chain (hR : Robertson) {M E : ℂ → ℂ}
    (hM : AnalyticOnNhd ℂ M disk) (hS : IsS (fun z => z * M (z ^ 2)))
    (hE : IsWeight E) {k : ℕ} (hk : 1 ≤ k) :
    let P := productTaylorPoly M k
    hardyTwoNorm (fun z => P.eval z * E z) * hardyTwoNorm P.eval ≤ hardyTwoNorm P.eval ^ 2 ∧
    hardyTwoNorm P.eval ^ 2 = ∑ j ∈ Finset.range k, ‖coeff j M‖ ^ 2 ∧
    (∑ j ∈ Finset.range k, ‖coeff j M‖ ^ 2) ≤ (k : ℝ) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman
variable {Ω : Set ℂ} {U : Set Sphere} {G : ℂ → Sphere} {w x : ℂ}

theorem HolomorphicFromSphereOn.comp_sphereHolomorphicOn {f : Sphere → ℂ}
    (hf : HolomorphicFromSphereOn f U) (hG : SphereHolomorphicOn G Ω) (hm : MapsTo G Ω U) :
    AnalyticOnNhd ℂ (f ∘ G) Ω := by sorry

namespace CenteredChart
variable (c : CenteredChart U w)

theorem inverse_comp_isSchwarz (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hzero : G 0 = (w : Sphere)) : IsSchwarz (c.inverse ∘ G) := by sorry

theorem inverse_comp_isSchwarz_of_param {φ : ℂ → ℂ} (hG : SphereHolomorphicOn G Ω)
    (hm : MapsTo G Ω U) (hφ : AnalyticOnNhd ℂ φ disk) (hφm : MapsTo φ disk Ω)
    (hcenter : G (φ 0) = (w : Sphere)) : IsSchwarz (c.inverse ∘ G ∘ φ) := by sorry

variable (d : CenteredChart U w)

theorem radius_eq : radius U w = ‖deriv (finitePart ∘ c.forward) 0‖ := by sorry

include c in

theorem radius_pos : 0 < radius U w := by sorry

theorem hypDistanceFrom_eq {v : Sphere} (hv : v ∈ U) :
    hypDistanceFrom U w v = Real.artanh ‖c.inverse v‖ := by sorry

theorem poleParam_eq (hp : OnePoint.infty ∈ U) : poleParam U w = ‖c.inverse OnePoint.infty‖ := by sorry

include c in

theorem poleParam_mem_Ioo (hp : OnePoint.infty ∈ U) : poleParam U w ∈ Ioo 0 1 := by sorry

end CenteredChart
end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology ComplexOrder
namespace Goodman

theorem coeff_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => f z * g z) =
      ∑ i ∈ Finset.range (n + 1), coeff i f * coeff (n - i) g := by sorry

theorem slit_coeff_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) (n : ℕ) (hn : 1 ≤ n) :
    (coeff n q).im = 0 ∧ 0 < (coeff n q).re := by sorry

theorem slit_pow_coeff_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) (k n : ℕ) :
    (coeff n (fun z => q z ^ k)).im = 0 ∧ 0 ≤ (coeff n (fun z => q z ^ k)).re := by sorry

theorem slit_square_coeff_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {n : ℕ} (hn : 2 ≤ n) :
    0 < (coeff n (fun z => q z ^ 2)).re := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem full_slit_coordinates {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f) :
    ∃ χ F : ℂ → ℂ, Bihol disk (slitDisk p) χ ∧ MapsTo χ disk (slitDisk p) ∧
      LeftInvOn χ q (slitDisk p) ∧ LeftInvOn q χ disk ∧ χ 0 = 0 ∧
      HasDerivAt χ (slitR p : ℂ) 0 ∧ IsS F ∧
      EqOn F (fun w => finitePart (f (χ w)) / (slitR p : ℂ)) disk ∧
      ∀ z ∈ slitDisk p, finitePart (f z) = (slitR p : ℂ) * F (q z) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem coeff_koebe (n : ℕ) : coeff n (fun z : ℂ => z/(1-z)^2) = (n:ℂ) := by sorry

theorem slit_weight_sum {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) (n : ℕ) :
    slitR p * (∑ k ∈ Finset.range (n+1), (k:ℝ) * (coeff n (fun z => q z ^ k)).re) =
      (coeff n (fun z => finitePart (extremal p z))).re := by sorry

end Goodman
end
end

section

noncomputable section
open Complex Filter InnerProductSpace Metric Set
open scoped Polynomial Topology
namespace Goodman

def poissonMajorant (P : ℂ[X]) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 w • fun ζ => ‖P.eval ζ‖) 0 1

theorem polynomial_norm_submean (P : ℂ[X]) (c : ℂ) (r : ℝ) :
    ‖P.eval c‖ ≤ Real.circleAverage (fun z => ‖P.eval z‖) c r := by sorry

theorem transfer_poisson (P : ℂ[X]) {w : ℂ} (hw : w ∈ disk) :
    ‖P.eval w‖ ≤ poissonMajorant P w := by sorry

theorem poissonMajorant_harmonic_comp (P : ℂ[X]) {h : ℂ → ℂ} (hh : IsSchwarz h) :
    HarmonicOnNhd (poissonMajorant P ∘ h) disk := by sorry

theorem poissonMajorant_zero (P : ℂ[X]) :
    poissonMajorant P 0 = Real.circleAverage (fun ζ => ‖P.eval ζ‖) 0 1 := by sorry

theorem transfer_mean (P : ℂ[X]) {h : ℂ → ℂ} (hh : IsSchwarz h) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) :
    Real.circleAverage (fun ζ => poissonMajorant P (h ((r : ℂ) * ζ))) 0 1 =
      poissonMajorant P 0 := by sorry

theorem transfer_mean_le_majorant (P : ℂ[X]) {h : ℂ → ℂ} (hh : IsSchwarz h) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) :
    Real.circleAverage (fun ζ => ‖P.eval (h ((r : ℂ) * ζ))‖) 0 1 ≤
      Real.circleAverage (fun ζ => poissonMajorant P (h ((r : ℂ) * ζ))) 0 1 := by sorry

theorem transfer_cauchy (P : ℂ[X]) {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h)
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    r^n * ‖coeff n (fun z => e z * P.eval (h z))‖ ≤
      Real.circleAverage (fun ζ => ‖P.eval (h ((r : ℂ) * ζ))‖) 0 1 := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem szapiel_zero_multiplier (h : ℂ → ℂ) :
    (fun w : ℂ => ∑ j ∈ Finset.range (0+1), coeff 0 (fun z => h z^j) * w^(0-j)) =
      fun _ => 1 := by sorry

theorem szapiel_unweighted_transfer {h : ℂ → ℂ} (hh : IsSchwarz h) (n : ℕ) :
    let P := fun w : ℂ => ∑ j ∈ Finset.range (n+1), coeff n (fun z => h z^j) * w^(n-j)
    IsWeight P ∧ P 0 = deriv h 0 ^ n ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 → coeff n (g ∘ h) = coeff n (fun w => P w * g w) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Topology Metric
namespace Goodman

theorem diskInverse_bihol {a : ℂ} (ha : a ∈ disk) : Bihol disk disk (diskInverse a) := by sorry

theorem riemannMapping_of_planarRiemannMapping (hR : PlanarRiemannMapping) : RiemannMapping := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem IsM.eqOn_of_germ {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : ℂ → Sphere}
    (hf : IsM p f) (hg : IsM p g) (h : (finitePart ∘ f) =ᶠ[𝓝 (0 : ℂ)] (finitePart ∘ g)) :
    EqOn f g disk := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman
variable {Ω : Set ℂ} {U : Set Sphere} {w x : ℂ} {G : ℂ → Sphere}

theorem SphereHolomorphicOn.comp_analyticOnNhd {V : Set ℂ} {φ : ℂ → ℂ}
    (hG : SphereHolomorphicOn G Ω) (hφ : AnalyticOnNhd ℂ φ V) (hm : MapsTo φ V Ω) :
    SphereHolomorphicOn (G ∘ φ) V := by sorry

namespace CenteredChart

theorem unit_maps_disk {r : ℂ} (hr : ‖r‖ = 1) :
    MapsTo (fun z => r * z) disk disk := by
  intro z hz
  simpa [disk, mem_ball_zero_iff, norm_mul, hr] using (mem_ball_zero_iff.mp hz : ‖z‖ < 1)

def rotate (c : CenteredChart U w) (r : ℂ) (hr : ‖r‖ = 1) : CenteredChart U w := by
  have hr0 : r ≠ 0 := norm_ne_zero_iff.mp (hr ▸ one_ne_zero)
  have hi : ‖r⁻¹‖ = 1 := by simp [hr]
  exact {
    forward := fun z => c.forward (r * z)
    inverse := fun y => r⁻¹ * c.inverse y
    forward_holo := c.forward_holo.comp_analyticOnNhd
      (fun _ _ => analyticAt_const.mul analyticAt_id) (unit_maps_disk hr)
    inverse_holo := ⟨fun z hz => analyticAt_const.mul (c.inverse_holo.1 z hz),
      fun hp => analyticAt_const.mul (c.inverse_holo.2 hp)⟩
    forward_maps := c.forward_maps.comp (unit_maps_disk hr)
    inverse_maps := (unit_maps_disk hi).comp c.inverse_maps
    left_inverse := fun z hz => by
      change r⁻¹ * c.inverse (c.forward (r * z)) = z
      rw [c.left_inverse (unit_maps_disk hr hz), inv_mul_cancel_left₀ hr0]
    right_inverse := fun y hy => by
      change c.forward (r * (r⁻¹ * c.inverse y)) = y
      rw [mul_inv_cancel_left₀ hr0, c.right_inverse hy]
    center := by simpa using c.center }

theorem exists_pole_rotation (c : CenteredChart U w) (hp : OnePoint.infty ∈ U) :
    ∃ (r : ℂ) (hr : ‖r‖ = 1), c.inverse OnePoint.infty = r * (poleParam U w : ℂ) ∧
      (c.rotate r hr).forward (poleParam U w : ℂ) = OnePoint.infty := by sorry

end CenteredChart

def normalizeValue (w a : ℂ) : Sphere → Sphere := OnePoint.map (fun v => (v - w) / a)

namespace CenteredChart
variable (c : CenteredChart U w)

def scale := deriv (finitePart ∘ c.forward) 0

def normalized : ℂ → Sphere := normalizeValue w c.scale ∘ c.forward

theorem scale_ne_zero : c.scale ≠ 0 := by sorry

theorem norm_scale : ‖c.scale‖ = radius U w := by sorry

theorem restore_normalized (z : ℂ) : restoreValue w c.scale (c.normalized z) = c.forward z := by sorry

theorem forward_bijOn : BijOn c.forward disk U := by sorry

theorem inverse_comp_bijOn_iff (hm : MapsTo G Ω U) :
    BijOn (c.inverse ∘ G) Ω disk ↔ BijOn G Ω U := by sorry

theorem normalized_germ :
    (finitePart ∘ c.normalized) =ᶠ[𝓝 0] fun z => (finitePart (c.forward z) - w) / c.scale := by sorry

theorem exists_rotated_isM (hp : OnePoint.infty ∈ U) :
    ∃ (r : ℂ) (hr : ‖r‖ = 1), c.inverse OnePoint.infty = r * (poleParam U w : ℂ) ∧
      IsM (poleParam U w) (c.rotate r hr).normalized := by sorry

theorem normalized_isS (hp : OnePoint.infty ∉ U) : IsS (finitePart ∘ c.normalized) := by sorry

theorem factorization_germ (hG : SphereHolomorphicOn G Ω) (hm : MapsTo G Ω U)
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hw : G x = (w : Sphere)) :
    (finitePart ∘ G) =ᶠ[𝓝 x] fun z => w + c.scale * finitePart (c.normalized (c.inverse (G z))) := by sorry

theorem coeff_factorization (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (finitePart ∘ G) = c.scale * coeff n (fun z => finitePart (c.normalized (c.inverse (G z)))) := by sorry

end CenteredChart
end Goodman
end
end

section

noncomputable section
open Complex Metric Set
open scoped ComplexConjugate Topology
namespace Goodman

def geomJet (k : ℕ) (w : ℂ) := ∑ j ∈ Finset.range k, w ^ j

def fejerKernel (k : ℕ) (w : ℂ) : ℝ := ‖geomJet k w‖ ^ 2 / k

theorem fejerKernel_nonneg (k : ℕ) (w : ℂ) : 0 ≤ fejerKernel k w := by sorry

def fejerMean (k : ℕ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k, z ^ j * (((k - j : ℕ) : ℂ) / k * coeff j E)

theorem coeff_fejerMean (E : ℂ → ℂ) {j k : ℕ} (hj : j < k) :
    coeff j (fejerMean k E) = ((k - j : ℕ) : ℂ) / k * coeff j E := by sorry

theorem fejerKernel_mass (m : ℕ) : Real.circleAverage (fejerKernel (m+1)) 0 1 = 1 := by sorry

theorem fejerMean_isWeight {E : ℂ → ℂ} (hE : IsWeight E) (m : ℕ) :
    IsWeight (fejerMean (m+1) E) := by sorry

theorem fejer_derivative_identity {H E : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (h0 : H 0 = 0) (hE : IsWeight E) (m : ℕ) :
    coeff m (fun z => deriv H z * E z) =
      ((m+1 : ℕ) : ℂ) * coeff (m+1) (fun z => H z * fejerMean (m+1) E z) := by sorry

theorem fejer_derivative_bound {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (h0 : H 0 = 0)
    {p : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hbound : ∀ W, IsWeight W → ‖coeff k (fun z => H z * W z)‖ ≤ A p k)
    {E : ℂ → ℂ} (hE : IsWeight E) :
    ‖coeff (k-1) (fun z => deriv H z * E z)‖ ≤ k * A p k := by sorry

end Goodman
end
end

section

noncomputable section
open Filter
open scoped Topology
namespace Goodman

theorem coeff_deriv_succ (f : ℂ → ℂ) (m : ℕ) :
    coeff m (deriv f) = (m + 1 : ℂ) * coeff (m + 1) f := by sorry

end Goodman
end
end

section

namespace Goodman
open Filter Set
open scoped Topology

theorem hasDerivAt_slit_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) : HasDerivAt q (1 / (slitR p : ℂ)) 0 := by sorry

end Goodman
end

section

noncomputable section
open Complex Filter MeasureTheory Metric Set
open scoped Polynomial Topology
namespace Goodman
open Real
local notation "𝕋" => AddCircle (2 * π)
attribute [local instance] Goodman.instFactLtRealOfNatHMulPi_goodman
local notation "σ" => (AddCircle.haarAddCircle (T := 2 * π))
local notation "ζ" => (fun θ : 𝕋 => (AddCircle.toCircle θ : ℂ))

theorem transfer_polynomial_L1 {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h)
    (n : ℕ) (P : ℂ[X]) :
    ‖coeff n (fun z => e z * P.eval (h z))‖ ≤ ∫ θ : 𝕋, ‖P.eval (ζ θ)‖ ∂σ := by sorry

theorem transfer_boundary_moments {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h) (n : ℕ) :
    ∃ (F : ℂ → ℂ) (v : C(𝕋, ℂ)),
      AnalyticOnNhd ℂ F (closedBall 0 1) ∧ MapsTo F (closedBall 0 1) (closedBall 0 1) ∧
      (∀ θ, ‖v θ‖ ≤ 1) ∧ (∀ θ, (ζ θ)^n * v θ = F (ζ θ)) ∧
      (∀ P : ℂ[X], coeff n (fun z => e z * P.eval (h z)) =
        ∫ θ : 𝕋, v θ * P.eval (ζ θ) ∂σ) ∧
      (∀ j : ℕ, n < j → (∫ θ : 𝕋, v θ * (ζ θ)^j ∂σ) = 0) ∧
      (∀ j : ℕ, j ≤ n → (∫ θ : 𝕋, v θ * (ζ θ)^j ∂σ) = coeff (n-j) F) ∧
      (∀ m : ℤ, fourierCoeff (fun θ : 𝕋 => (ζ θ)^n * v θ) m =
        if m < 0 then 0 else coeff m.toNat F) := by sorry

theorem transfer_L1_extension {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h) (n : ℕ) :
    ∃ (v : Lp ℂ ⊤ σ) (L : Lp ℂ 1 σ →L[ℂ] ℂ), ‖v‖ ≤ 1 ∧ ‖L‖ ≤ 1 ∧
      (∀ᵐ θ ∂σ, ‖v θ‖ ≤ 1) ∧ (∀ f, L f = ∫ θ, v θ * f θ ∂σ) ∧
      ∀ P : ℂ[X], L (ContinuousMap.toLp 1 σ ℂ P.toAddCircle) =
        coeff n (fun z => e z * P.eval (h z)) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

def diskForward (a z : ℂ) : ℂ := (a + z) / (1 + star a * z)

theorem diskForward_bihol {a : ℂ} (ha : a ∈ disk) : Bihol disk disk (diskForward a) := by sorry

theorem diskForward_zero (a : ℂ) : diskForward a 0 = a := by sorry

theorem radius_planeDomain_disk {a : ℂ} (ha : a ∈ disk) :
    radius (planeDomain disk) a = 1 - ‖a‖ ^ 2 := by sorry

def diskKernel (b z : ℂ) : ℂ := z / (1 - b * z)

theorem diskInverse_affine {a : ℂ} (ha : a ∈ disk) (z : ℂ) :
    diskInverse a (a + ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * z) = diskKernel (star a) z := by sorry

theorem coeff_diskKernel_pow (b : ℂ) {m j : ℕ} (hj : j ≤ m) :
    coeff (m + 1) (fun z => diskKernel b z ^ (j + 1)) =
      (m.choose j : ℂ) * b ^ (m-j) := by sorry

theorem coeff_comp_diskKernel {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (b : ℂ) (m : ℕ) :
    coeff (m+1) (F ∘ diskKernel b) =
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℂ) * b ^ (m-j) * coeff (j+1) F := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem koebe_of_second_eq_two {F : ℂ → ℂ} (hF : IsS F) (h2 : BieberbachSecondRigidity)
    (he : coeff 2 F = 2) : EqOn F (fun z => z / (1 - z)^2) disk := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman
variable {U : Set Sphere} {w : ℂ} {G : ℂ → Sphere}

theorem CenteredChart.norm_coeff_weighted_factor (c : CenteredChart U w)
    (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U) (hw : G 0 = (w : Sphere))
    (E : ℂ → ℂ) (k : ℕ) :
    ‖coeff k (fun z => E z * ((finitePart (G z) - w) / (radius U w : ℂ)))‖ =
      ‖coeff k (fun z => E z * finitePart (c.normalized (c.inverse (G z))))‖ := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem IsRotation.bijOn_disk {f : ℂ → ℂ} (hf : IsRotation f) : BijOn f disk disk := by sorry

end Goodman
end
end

section

noncomputable section
open Set Metric Filter
open scoped Topology
namespace Goodman

def realSlitSegment (l r : ℝ) : Set Sphere :=
  planeDomain (Complex.ofReal '' Icc l r)

def joukowskiSphere (z : ℂ) : Sphere :=
  if z = 0 then OnePoint.infty else ((z + z⁻¹ : ℂ) : Sphere)

theorem extremal_image_disk {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    extremal p '' disk =
      (realSlitSegment (-1 / (p + 1 / p - 2)) (-1 / (p + 1 / p + 2)))ᶜ := by sorry

theorem affine_extremal_image_disk (w : ℂ) {a : ℂ} (ha : a ≠ 0) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (restoreValue w a ∘ extremal p) '' disk =
      (planeDomain (segment ℝ
        (w + a * ↑(-1 / (p + 1 / p - 2))) (w + a * ↑(-1 / (p + 1 / p + 2)))))ᶜ := by sorry

theorem affine_extremal_segmentOnLineThrough (w : ℂ) {a : ℂ} (ha : a ≠ 0) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    IsSegmentOnLineThrough (((restoreValue w a ∘ extremal p) '' disk)ᶜ) w := by sorry

theorem affine_extremal_invariants (w : ℂ) {a : ℂ} (ha : a ≠ 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    let U := (restoreValue w a ∘ extremal p) '' disk
    poleParam U w = p ∧ radius U w = ‖a‖ := by sorry

def segmentPole (near far : ℝ) : ℝ :=
  (Real.sqrt far - Real.sqrt near) / (Real.sqrt far + Real.sqrt near)

theorem segment_parameters {l r : ℝ} (hl : 0 < l) (hlr : l < r) :
    let p := segmentPole l r
    let m := segmentScale l r
    0 < p ∧ p < 1 ∧ 0 < m ∧
      m / (p + 1 / p + 2) = l ∧ m / (p + 1 / p - 2) = r := by sorry

theorem segment_ordered_endpoints {K : Set Sphere} {w : ℂ}
    (hK : IsSegmentOnLineThrough K w) (hw : (w : Sphere) ∉ K) :
    ∃ ξ η u : ℂ, K = planeDomain (segment ℝ ξ η) ∧
      0 < ‖w-ξ‖ ∧ ‖w-ξ‖ < ‖w-η‖ ∧ ‖u‖ = 1 ∧
      w-ξ = (‖w-ξ‖ : ℂ)*u ∧ w-η = (‖w-η‖ : ℂ)*u := by sorry

theorem segment_converse {K : Set Sphere} {w : ℂ} (hK : IsSegmentOnLineThrough K w)
    (hw : (w : Sphere) ∉ K) :
    ∃ (ξ η : ℂ) (p : ℝ) (a : ℂ), K = planeDomain (segment ℝ ξ η) ∧
      0 < ‖w-ξ‖ ∧ ‖w-ξ‖ < ‖w-η‖ ∧
      p = segmentPole ‖w-ξ‖ ‖w-η‖ ∧ 0 < p ∧ p < 1 ∧
      ‖a‖ = segmentScale ‖w-ξ‖ ‖w-η‖ ∧ a ≠ 0 ∧ a / (‖a‖ : ℂ) = (w-ξ)/(‖w-ξ‖ : ℂ) ∧
      (restoreValue w a ∘ extremal p) 0 = (w : Sphere) ∧
      (restoreValue w a ∘ extremal p) p = OnePoint.infty ∧
      BijOn (restoreValue w a ∘ extremal p) disk Kᶜ := by sorry

theorem segment_intrinsic_parameters {K : Set Sphere} {w : ℂ}
    (hK : IsSegmentOnLineThrough K w) (hw : (w : Sphere) ∉ K) :
    ∃ ξ η : ℂ, K = planeDomain (segment ℝ ξ η) ∧ 0 < ‖w-ξ‖ ∧ ‖w-ξ‖ < ‖w-η‖ ∧
      poleParam Kᶜ w = segmentPole ‖w-ξ‖ ‖w-η‖ ∧
      radius Kᶜ w = segmentScale ‖w-ξ‖ ‖w-η‖ := by sorry

end Goodman
end
end

section

noncomputable section
open Complex Metric
open scoped ComplexConjugate
namespace Goodman

theorem fejerKernel_eq_laurent {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : ‖w‖ = 1) :
    (fejerKernel k w : ℂ) = ∑ j ∈ Finset.Ioo (-(k : ℤ)) (k : ℤ),
      (1 - (j.natAbs : ℂ) / k) * w ^ j := by sorry

theorem fejerMean_eq_circleAverage_conj {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E disk)
    {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : z ∈ disk) :
    fejerMean k E z = Real.circleAverage
      (fun w => E (z * conj w) * (fejerKernel k w : ℂ)) 0 1 := by sorry

theorem centered_coeff_zero {φ : ℂ → ℂ} {G : ℂ → Sphere} {x w : ℂ}
    (U : Set Sphere) (hφ : φ 0 = x) (hG : G x = (w : Sphere)) :
    coeff 0 (fun z => (finitePart (G (φ z)) - w) / (radius U w : ℂ)) = 0 := by sorry

theorem IsWeight.pow {v : ℂ → ℂ} (hv : IsWeight v) (j : ℕ) :
    IsWeight (fun z => v z ^ j) := by sorry

end Goodman
end
end

section

noncomputable section
open Filter
open scoped Topology
namespace Goodman

theorem lagrange_inversion_coeff {s g H : ℂ → ℂ} (hs : AnalyticAt ℂ s 0)
    (hs0 : s 0 = 0) (hs1 : deriv s 0 = 1) (hg : AnalyticAt ℂ g 0)
    (hH : H =ᶠ[𝓝 0] g ∘ s) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) * coeff n g =
      coeff (n - 1) (fun z => deriv H z * (1 / dslope s 0 z) ^ n) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

def centeredPullback (G : ℂ → Sphere) (φ : ℂ → ℂ) (U : Set Sphere) (w z : ℂ) : ℂ :=
  (finitePart (G (φ z)) - w) / (radius U w : ℂ)

variable {Ω : Set ℂ} {U : Set Sphere} {G : ℂ → Sphere} {φ : ℂ → ℂ} {a w : ℂ}

theorem disk_centered_germ (c : CenteredChart U w) (ha : a ∈ disk)
    (hG : SphereHolomorphicOn G disk) (hw : G a = (w : Sphere)) :
    (fun z => G (a + (radius (planeDomain disk) a : ℂ) * z)) =ᶠ[𝓝 0]
      fun z => ((w + (radius U w : ℂ) *
        centeredPullback G (diskForward a) U w (diskKernel (star a) z) : ℂ) : Sphere) := by sorry

theorem disk_derivative_sum (ha : a ∈ disk) (hG : SphereHolomorphicOn G disk)
    (hw : G a = (w : Sphere)) {n : ℕ} (hn : 0 < n) :
    (radius (planeDomain disk) a : ℂ) ^ n * iteratedDeriv n (finitePart ∘ G) a /
        ((n.factorial : ℂ) * (radius U w : ℂ)) =
      ∑ j ∈ Finset.range n, ((n-1).choose j : ℂ) * star a ^ (n-1-j) *
        coeff (j+1) (centeredPullback G (diskForward a) U w) := by sorry

theorem disk_derivative_of_first_coeffs (ha : a ∈ disk) (hG : SphereHolomorphicOn G disk)
    (hw : G a = (w : Sphere)) {n : ℕ} (hn : 0 < n)
    (hb : ∀ k, 1 ≤ k → k ≤ n →
      ‖coeff k (centeredPullback G (diskForward a) U w)‖ ≤ A (poleParam U w) k) :
    derivativeRatio n G a (radius (planeDomain disk) a) (radius U w) ≤
      D (poleParam U w) ‖a‖ n := by sorry

theorem convex_source_normalize (hc : Convex ℝ Ω) (hφ : Bihol disk Ω φ)
    (hφ0 : φ 0 = a) (hd : deriv φ 0 = (radius (planeDomain Ω) a : ℂ)) :
    let s := fun z => (φ z - a) / (radius (planeDomain Ω) a : ℂ)
    let σ := Function.invFunOn s disk
    IsS s ∧ Convex ℝ (s '' disk) ∧ σ 0 = 0 ∧ AnalyticAt ℂ σ 0 ∧
      σ ∘ s =ᶠ[𝓝 0] id ∧ s ∘ σ =ᶠ[𝓝 0] id := by sorry

theorem convex_centered_germ (c : CenteredChart U w) (hc : Convex ℝ Ω)
    (hφ : Bihol disk Ω φ) (hφ0 : φ 0 = a) (hd : deriv φ 0 = (radius (planeDomain Ω) a : ℂ))
    (hG : SphereHolomorphicOn G Ω) (hw : G a = (w : Sphere)) :
    let r : ℂ := radius (planeDomain Ω) a
    let s := fun z => (φ z - a) / r
    let σ := Function.invFunOn s disk
    let H := centeredPullback G φ U w
    ((fun z => G (a + r*z)) =ᶠ[𝓝 0] fun z => ((w + (radius U w : ℂ) * H (σ z) : ℂ) : Sphere)) ∧
      ∀ n : ℕ, 0 < n → coeff n (H ∘ σ) =
        r ^ n * iteratedDeriv n (finitePart ∘ G) a / ((n.factorial : ℂ) * (radius U w : ℂ)) := by sorry

theorem convex_top_coeff {H v : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (hv : AnalyticAt ℂ v 0)
    {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    coeff (n-1) (fun z => deriv H z * z^j * v z^j) =
      if j = n then 0 else coeff (n-j-1) (fun z => deriv H z * v z^j) := by sorry

theorem convex_binomial_factor {j n : ℕ} (hj : j < n) :
    ((n-j : ℕ) : ℝ) * n.choose j / n = ((n-1).choose (n-j-1) : ℝ) := by sorry

theorem convex_binomial_sum (p : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (((n-j : ℕ) : ℝ) * n.choose j / n) * A p (n-j)) = D p 1 n := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman
variable {p : ℝ} {q : ℂ → ℂ}

theorem slit_inverse_chart (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    ∃ χ : ℂ → ℂ, Bihol disk (slitDisk p) χ ∧ LeftInvOn χ q (slitDisk p) ∧
      LeftInvOn q χ disk ∧ χ 0 = 0 ∧ HasDerivAt χ (slitR p : ℂ) 0 := by sorry

theorem radius_slitDisk (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    radius (planeDomain (slitDisk p)) 0 = 4 * p / (1 + p)^2 := by sorry

theorem slitC_pos (hp : 0 < p) (hp1 : p < 1) : 0 < slitC p := by sorry

theorem slitC_eq_inv_radius_sub_one (hp : 0 < p) : slitC p = 1 / slitR p - 1 := by sorry

theorem joukowski_add_two {z : ℂ} (hz : z ≠ 0) : z + z⁻¹ + 2 = (1 + z)^2 / z := by sorry

theorem slit_difference_factor (w z : ℂ) :
    w * (1+z)^2 - z * (1+w)^2 = (w-z) * (1-z*w) := by sorry

theorem slit_factorization (hp : 0 < p) (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) :
    (q z - z) * (1 - z * q z) = (slitC p : ℂ) * z * (1 + q z)^2 := by sorry

theorem slit_geometric_recurrence (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun m : ℕ => (z * q z)^m) (1 - z * q z)⁻¹ ∧
      q z = z + (slitC p : ℂ) * z * (1 + q z)^2 * ∑' m : ℕ, (z * q z)^m := by sorry

theorem slit_coeff_one (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    coeff 1 q = 1 + (slitC p : ℂ) := by sorry

theorem slit_coeff_polynomial (n : ℕ) :
    ∃ P : MvPolynomial (Fin (n+2)) ℕ, ∀ {p : ℝ} {q : ℂ → ℂ},
      0 < p → p < 1 → IsSlitMap p q →
      coeff (n+2) q = 2 * (slitC p : ℂ) * coeff (n+1) q +
        MvPolynomial.eval₂Hom (Nat.castRingHom ℂ)
          (fun i : Fin (n+2) => if i.val = 0 then (slitC p : ℂ) else coeff i q) P := by sorry

open scoped ComplexOrder in

theorem slit_coeff_lower_bound (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q)
    {n : ℕ} (hn : 2 ≤ n) : 2 * slitC p * (coeff (n-1) q).re ≤ (coeff n q).re := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem theorem_one_bound (H1 : Robertson) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e →
    ∀ n : ℕ, 1 ≤ n → ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤ A p n := by sorry

theorem theorem_one_higher_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h → ∀ n : ℕ, 2 ≤ n →
    (‖coeff n (fun z => finitePart (f (h z)))‖ = A p n ↔
      EqOn f (extremal p) disk ∧ IsRotation h) := by sorry

theorem theorem_one_first_equality :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ (f : ℂ → Sphere), IsM p f →
    ∀ h : ℂ → ℂ, IsSchwarz h →
    (‖coeff 1 (fun z => finitePart (f (h z)))‖ = A p 1 ↔ IsRotation h) := by sorry

theorem lemma_four :
  ∀ h : ℂ → ℂ, IsSchwarz h → ∀ e : ℂ → ℂ, IsWeight e → ∀ n : ℕ,
    ∃ E : ℂ → ℂ, IsWeight E ∧ E 0 = e 0 * (deriv h 0)^n ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 →
        coeff n (fun z => e z * g (h z)) = coeff n (fun w => E w * g w) := by sorry

theorem lemma_five :
  ∀ (p : ℝ), 0 < p → p < 1 → ∃ q : ℂ → ℂ, IsSlitMap p q ∧
    (∀ n : ℕ, 1 ≤ n → (coeff n q).im = 0 ∧ 0 < (coeff n q).re) ∧
    (∀ᶠ z in 𝓝 (0 : ℂ), HasSum
      (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (finitePart (extremal p z))) := by sorry

theorem lemma_six (H1 : Robertson) :
  ∀ F : ℂ → ℂ, IsS F → ∀ E : ℂ → ℂ, IsWeight E →
    ∀ k : ℕ, 1 ≤ k → ‖coeff k (fun z => F z * E z)‖ ≤ (k : ℝ) := by sorry

theorem proposition_seven (H1 : Robertson) :
  ∀ (p : ℝ), 0 < p → p < 1 → ∀ q : ℂ → ℂ, IsSlitMap p q →
    ∀ f : ℂ → Sphere, IsM p f → ∀ E : ℂ → ℂ, IsWeight E →
    ∀ n : ℕ, 1 ≤ n →
      ‖coeff n (fun z => E z * finitePart (f z))‖ ≤
        A p n - slitR p * (coeff n q).re * (1 - ‖E 0‖) := by sorry

theorem base_coefficient_bound (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (finitePart ∘ f)‖ ≤ A p n := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric Topology
open scoped Topology
namespace Goodman

def diskPhase (a : ℂ) : ℂ := if a = 0 then 1 else star a / (‖a‖ : ℂ)

theorem norm_diskPhase (a : ℂ) : ‖diskPhase a‖ = 1 := by sorry

theorem star_eq_diskPhase_mul_norm (a : ℂ) : star a = diskPhase a * (‖a‖ : ℂ) := by sorry

theorem diskPhase_real {a : ℂ} (him : a.im = 0) (hre : 0 ≤ a.re) : diskPhase a = 1 := by sorry

theorem coeff_disk_model {p : ℝ} (hp : 0 < p) (a : ℂ) (m : ℕ) :
    coeff (m+1) (fun z => finitePart (extremal p (diskPhase a * diskKernel (star a) z))) =
      diskPhase a ^ (m+1) * (D p ‖a‖ (m+1) : ℂ) := by sorry

theorem disk_model_derivativeRatio {p : ℝ} (hp : 0 < p) {a : ℂ} (ha : a ∈ disk)
    {n : ℕ} (hn : 1 ≤ n) :
    derivativeRatio n (fun z => extremal p (diskPhase a * diskInverse a z)) a
      (radius (planeDomain disk) a) 1 = D p ‖a‖ n := by sorry

theorem extremal_model_data {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn (extremal p) disk ∧
      radius (extremalTarget p) 0 = 1 ∧ poleParam (extremalTarget p) 0 = p := by sorry

theorem diskSharpModel : DiskSharpModel := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem figure3_segment :
    extremal (1/2) '' disk = (realSlitSegment (-2) (-2/9))ᶜ ∧
    OnePoint.infty ∈ extremal (1/2) '' disk ∧ extremal (1/2) 0 = (0 : ℂ) := by sorry

def slitArcPoint (p s x : ℝ) : ℂ :=
  ⟨slitArcRe p x, s * Real.sqrt (1 - slitArcRe p x ^ 2)⟩

def slitBank (p s : ℝ) : Set ℂ := slitDisk p ∩ {z | 0 < s * z.im}

theorem slitMap_bank_limit {p s x : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hq : IsSlitMap p q)
    (hs : s = 1 ∨ s = -1) (hx : x ∈ Icc p 1) :
    Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 (slitArcPoint p s x)) := by sorry

theorem slitMap_tip_limit {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hq : IsSlitMap p q) :
    Tendsto q (𝓝[slitDisk p] (p : ℂ)) (𝓝 1) := by sorry

theorem slitMap_bank_trace {p s : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hp1 : p < 1)
    (hq : IsSlitMap p q) (hs : s = 1 ∨ s = -1) (w : ℂ) :
    (∃ x ∈ Icc p 1, Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 w)) ↔
      ‖w‖ = 1 ∧ 2 * slitR p - 1 ≤ w.re ∧ 0 ≤ s*w.im := by sorry

theorem slitMap_bank_trace_Ico {p s : ℝ} {q : ℂ → ℂ} (hp : 0 < p) (hp1 : p < 1)
    (hq : IsSlitMap p q) (hs : s = 1 ∨ s = -1) (w : ℂ) :
    (∃ x ∈ Ico p 1, Tendsto q (𝓝[slitBank p s] (x : ℂ)) (𝓝 w)) ↔
      ‖w‖ = 1 ∧ 2 * slitR p - 1 < w.re ∧ 0 ≤ s*w.im := by sorry

theorem figure2_arc {q : ℂ → ℂ} (hq : IsSlitMap (1/2) q) (w : ℂ) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ x ∈ Icc (1/2 : ℝ) 1,
      Tendsto q (𝓝[slitBank (1/2) s] (x : ℂ)) (𝓝 w)) ↔
    ‖w‖ = 1 ∧ 7/9 ≤ w.re := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman
variable {U : Set Sphere} {G : ℂ → Sphere} {w : ℂ}

theorem CenteredChart.exists_rotate_eqOn_of_bijOn (c : CenteredChart U w)
    (hG : SphereHolomorphicOn G disk) (hb : BijOn G disk U) (hw : G 0 = (w : Sphere)) :
    ∃ (r : ℂ) (hr : ‖r‖ = 1), EqOn (c.rotate r hr).forward G disk := by sorry

theorem geometric_equality_of_segment (hG : SphereHolomorphicOn G disk) (hb : BijOn G disk U)
    (hw : G 0 = (w : Sphere)) (hseg : IsSegmentOnLineThrough Uᶜ w) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (finitePart ∘ G)‖ = radius U w * A (poleParam U w) n := by sorry

end Goodman
end
end

section

noncomputable section
open Set Metric Filter
open scoped Topology
namespace Goodman

theorem convex_reciprocal_weight (hMS : MarxStrohhacker) {s : ℂ → ℂ}
    (hs : IsS s) (hc : Convex ℝ (s '' disk)) :
    ∃ v, IsWeight v ∧ EqOn (fun z => 1 / dslope s 0 z) (fun z => 1 + z * v z) disk := by sorry

theorem convex_binomial_coeff {H v : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (hv : AnalyticAt ℂ v 0) (m : ℕ) :
    coeff m (fun z => deriv H z * (1 + z * v z)^(m+1)) =
      ∑ i ∈ Finset.range (m+1), ((m+1).choose (i+1) : ℂ) *
        coeff i (fun z => deriv H z * v z ^ (m-i)) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem base_reduction_from_schlicht
    (hB : ∀ F : ℂ → ℂ, IsS F → ∀ k : ℕ, 1 ≤ k → ‖coeff k F‖ ≤ (k : ℝ))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere} (hf : IsM p f)
    {n : ℕ} (hn : 1 ≤ n) : ‖coeff n (finitePart ∘ f)‖ ≤ A p n := by sorry

end Goodman
end
end

section

noncomputable section
open Set
namespace Goodman

theorem lemma_eight (H1 : Robertson) (H4 : PlanarRiemannMapping) :
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ),
    IsSource Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U → G x = (w : Sphere) →
    ∀ φ : ℂ → ℂ, Bihol disk Ω φ → φ 0 = x → deriv φ 0 = (radius (planeDomain Ω) x : ℂ) →
    ∀ E : ℂ → ℂ, IsWeight E → ∀ k : ℕ, 1 ≤ k →
      ‖coeff k (fun z => E z * ((finitePart (G (φ z)) - w) / (radius U w : ℂ)))‖ ≤
        A (poleParam U w) k := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

theorem schwarz_of_disk_factor {ω : ℂ → ℂ} (hω : AnalyticOnNhd ℂ ω disk)
    (hm : MapsTo ω disk disk) : IsSchwarz (fun z => z * ω z) ∧ ‖deriv (fun z => z * ω z) 0‖ < 1 := by sorry

theorem strict_of_disk_factor (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {ω : ℂ → ℂ} (hω : AnalyticOnNhd ℂ ω disk)
    (hm : MapsTo ω disk disk) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => finitePart (f (z * ω z)))‖ < A p n := by sorry

theorem dilation_modulus {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖coeff n (fun z => finitePart (extremal p ((r : ℂ)*z)))‖ = r^n * A p n := by sorry

theorem dilation_sharp_limit {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => ‖coeff n (fun z => finitePart (extremal p ((r : ℂ)*z)))‖)
      (𝓝[<] (1:ℝ)) (𝓝 (A p n)) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem weighted_slit_pullback (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f)
    {E : ℂ → ℂ} (hE : IsWeight E) :
    ∃ χ F : ℂ → ℂ, Bihol disk (slitDisk p) χ ∧ IsS F ∧ IsWeight (E ∘ χ) ∧
    EqOn F (fun w => finitePart (f (χ w)) / (slitR p : ℂ)) disk ∧
    (∀ z ∈ slitDisk p, E z * finitePart (f z) = (slitR p : ℂ) * (F (q z) * E (χ (q z)))) ∧
    coeff 1 (fun w => F w * E (χ w)) = E 0 ∧
    ∀ k : ℕ, 1 ≤ k → ‖coeff k (fun w => F w * E (χ w))‖ ≤ (k : ℝ) := by sorry

theorem full_slit_restoration (H1 : Robertson) (H2 : BieberbachSecondRigidity)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ} (hq : IsSlitMap p q)
    {f : ℂ → Sphere} (hf : IsM p f) {n : ℕ} (hn : 2 ≤ n)
    (heq : ‖coeff n (finitePart ∘ f)‖ = A p n) :
    ∃ F : ℂ → ℂ, IsS F ∧ EqOn F (fun z => z/(1-z)^2) disk ∧
      ∀ z ∈ slitDisk p, finitePart (f z) = (slitR p : ℂ)*F (q z) ∧
        (slitR p : ℂ)*F (q z) = finitePart (extremal p z) := by sorry

end Goodman
end
end

section

noncomputable section
open Set Metric
namespace Goodman

theorem halfPlane_inverse_maps : MapsTo (fun x : ℂ => x/(1-x)) halfPlane disk := by sorry

theorem halfPlane_inverse_analytic : AnalyticOnNhd ℂ (fun x : ℂ => x/(1-x)) halfPlane := by sorry

theorem halfPlane_bihol : Bihol disk halfPlane (fun w : ℂ => w/(1+w)) := by sorry

theorem radius_halfPlane_zero : radius (planeDomain halfPlane) 0 = 1 := by sorry

theorem coeff_halfPlane_model {p : ℝ} (hp : 0 < p) (m : ℕ) :
    coeff (m+1) (fun x : ℂ => finitePart (extremal p (x/(1-x)))) = (D p 1 (m+1) : ℂ) := by sorry

theorem convexSharpModel : ConvexSharpModel := by sorry

end Goodman
end
end

section

noncomputable section
open Set Metric Filter
open scoped Topology
namespace Goodman

def slitB (p : ℝ) : ℝ := p + 1 / p

theorem joukowskiSphere_zero : joukowskiSphere 0 = OnePoint.infty := by sorry

theorem extremal_eq_reciprocal_joukowski {p : ℝ} (hp : p ≠ 0) :
    extremal p = moveOmitted ((slitB p : ℂ) : Sphere) ∘ joukowskiSphere := by sorry

theorem joukowskiSphere_bijOn_disk :
    BijOn joukowskiSphere disk (realSlitSegment (-2) 2)ᶜ := by sorry

theorem joukowskiReal_strictAnti {p : ℝ} (hp : 0 < p) :
    StrictAntiOn slitB (Icc p 1) := by sorry

theorem joukowskiReal_tendsto_one_left : Tendsto slitB (𝓝[<] (1 : ℝ)) (𝓝 2) := by sorry

theorem joukowskiSphere_image_radius {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    joukowskiSphere '' (Complex.ofReal '' Ico p 1) =
      planeDomain (Complex.ofReal '' Ioc 2 (slitB p)) := by sorry

theorem joukowskiSphere_image_slitDisk {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    joukowskiSphere '' slitDisk p = (realSlitSegment (-2) (slitB p))ᶜ := by sorry

theorem slitJoukowskiAffine_infty (p : ℝ) :
    slitJoukowskiAffine p OnePoint.infty = OnePoint.infty := by sorry

theorem slitJoukowskiAffine_endpoints {p : ℝ} (hp : 0 < p) :
    slitJoukowskiAffine p ((-2 : ℂ) : Sphere) = ((-2 : ℂ) : Sphere) ∧
    slitJoukowskiAffine p ((slitB p : ℂ) : Sphere) = ((2 : ℂ) : Sphere) := by sorry

theorem slitJoukowskiAffine_image_compl {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    slitJoukowskiAffine p '' (realSlitSegment (-2) (slitB p))ᶜ =
      (realSlitSegment (-2) 2)ᶜ := by sorry

def joukowskiDiskInverse : Sphere → ℂ := Function.invFunOn joukowskiSphere disk

theorem joukowskiDiskInverse_infty : joukowskiDiskInverse OnePoint.infty = 0 := by sorry

def joukowskiSlitMap (p : ℝ) : ℂ → ℂ :=
  joukowskiDiskInverse ∘ slitJoukowskiAffine p ∘ joukowskiSphere

theorem joukowskiSlitMap_zero (p : ℝ) : joukowskiSlitMap p 0 = 0 := by sorry

theorem slitMap_eqOn_joukowskiSlitMap {p : ℝ} {q : ℂ → ℂ} (hq : IsSlitMap p q) :
    EqOn q (joukowskiSlitMap p) (slitDisk p) := by sorry

theorem joukowskiSlitMap_isSlitMap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IsSlitMap p (joukowskiSlitMap p) := by sorry

theorem slitMap_joukowski_sub_two_sphere {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p)
    (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) :
    OnePoint.map (fun w : ℂ => w - 2) (joukowskiSphere (q z)) =
      OnePoint.map (fun v : ℂ => (slitR p : ℂ) * (v - (slitB p : ℂ))) (joukowskiSphere z) := by sorry

theorem joukowski_reciprocal_two_hasSum {w : ℂ} (hw : w ∈ disk) :
    HasSum (fun k : ℕ => (k : ℂ) * w ^ k) (w / (1 - w)^2) ∧
    moveOmitted ((2 : ℂ) : Sphere) (joukowskiSphere w) = ((w / (1 - w)^2 : ℂ) : Sphere) := by sorry

theorem slitMap_rational_majorant {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p)
    (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) :
    let d := 1 - (slitB p : ℂ) * z + z^2
    d ≠ 0 ∧ (slitR p : ℂ) * (q z / (1 - q z)^2) = z / d ∧
      HasSum (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (z / d) ∧
      extremal p z = ((z / d : ℂ) : Sphere) := by sorry

theorem extremal_joukowski_image {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    let B := slitB p
    2 < B ∧ -1 / (B-2) < -1 / (B+2) ∧ -1 / (B+2) < 0 ∧
    extremal p '' disk = (realSlitSegment (-1 / (B-2)) (-1 / (B+2)))ᶜ ∧
    extremal p 0 = (0 : ℂ) ∧ extremal p p = OnePoint.infty ∧
    OnePoint.infty ∈ extremal p '' disk := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem IsM.composition_holomorphic {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f)
    {h : ℂ → ℂ} (hh : IsSchwarz h) : SphereHolomorphicOn (f ∘ h) disk := by sorry

theorem IsM.composition_poles {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere}
    (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {x : ℂ} (hx : x ∈ disk) :
    (f (h x) = OnePoint.infty ↔ h x = p) ∧
    (∀ᶠ z in 𝓝[≠] x, f (h z) ≠ OnePoint.infty) := by sorry

theorem IsM.taylor_in_inner_disk {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {z : ℂ} (hz : ‖z‖ < p) :
    HasSum (fun n : ℕ => coeff n (fun t => finitePart (f (h t))) * z^n) (finitePart (f (h z))) := by sorry

theorem IsM.normalized_coefficients {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f) :
    coeff 0 (finitePart ∘ f) = 0 ∧ coeff 1 (finitePart ∘ f) = 1 := by sorry

theorem noninjective_composition_example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IsM p (extremal p) ∧ IsSchwarz (fun _ : ℂ => 0) ∧
    ¬ InjOn (extremal p ∘ (fun _ : ℂ => (0:ℂ))) disk := by sorry

theorem unweighted_goodman (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => finitePart (f (h z)))‖ ≤ A p n := by sorry

theorem base_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere} (hf : IsM p f)
    {n : ℕ} (hn : 2 ≤ n) : ‖coeff n (finitePart ∘ f)‖ = A p n ↔ EqOn f (extremal p) disk := by sorry

theorem rogosinski_weighted (H1 : Robertson) {F h e : ℂ → ℂ} (hF : IsS F)
    (hh : IsSchwarz h) (he : IsWeight e) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => e z * F (h z))‖ ≤ (n : ℝ) := by sorry

end Goodman
end
end

section

noncomputable section
open Set
namespace Goodman

theorem theorem_two_bound (H1 : Robertson) (H4 : PlanarRiemannMapping)
    {U : Set Sphere} (hU : IsTarget U) (hi : OnePoint.infty ∈ U)
    {G : ℂ → Sphere} {w : ℂ} (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) :
    (0 < poleParam U w ∧ poleParam U w < 1) ∧
    ∀ n : ℕ, 1 ≤ n → ‖coeff n (finitePart ∘ G)‖ ≤ radius U w * A (poleParam U w) n := by sorry

theorem theorem_two_equality (H1 : Robertson) (H2 : BieberbachSecondRigidity) (H4 : PlanarRiemannMapping)
    {U : Set Sphere} (hU : IsTarget U) (hi : OnePoint.infty ∈ U)
    {G : ℂ → Sphere} {w : ℂ} (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) {n : ℕ} (hn : 2 ≤ n) :
    ‖coeff n (finitePart ∘ G)‖ = radius U w * A (poleParam U w) n ↔
      BijOn G disk U ∧ IsSegmentOnLineThrough Uᶜ w := by sorry

theorem theorem_three_disk (H1 : Robertson) (H4 : PlanarRiemannMapping) :
  ∀ (U : Set Sphere) (x w : ℂ), IsTarget U → x ∈ disk →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G disk → MapsTo G disk U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain disk) x) (radius U w) ≤ D (poleParam U w) ‖x‖ n := by sorry

theorem theorem_three_convex (H1 : Robertson) (H3 : MarxStrohhacker) (H4 : PlanarRiemannMapping) :
  ∀ (Ω : Set ℂ) (U : Set Sphere) (x w : ℂ), IsSource Ω → Convex ℝ Ω → x ∈ Ω → IsTarget U →
    ∀ G : ℂ → Sphere, SphereHolomorphicOn G Ω → MapsTo G Ω U →
    G x = (w : Sphere) → ∀ n : ℕ, 2 ≤ n →
      derivativeRatio n G x (radius (planeDomain Ω) x) (radius U w) ≤ D (poleParam U w) 1 n := by sorry

theorem theorem_three_disk_extremal :
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ x ∈ disk,
  ∃ η : ℂ, ‖η‖ = 1 ∧ (x.im = 0 → 0 ≤ x.re → η = 1) ∧
    let G := fun z => extremal p (η * diskInverse x z)
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G disk ∧ MapsTo G disk (extremalTarget p) ∧
    G x = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G x (radius (planeDomain disk) x)
      (radius (extremalTarget p) 0) = D p ‖x‖ n := by sorry

theorem theorem_three_convex_extremal :
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    let G := fun z : ℂ => extremal p (z / (1-z))
    IsSource halfPlane ∧ Convex ℝ halfPlane ∧ (0 : ℂ) ∈ halfPlane ∧
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn G halfPlane ∧ MapsTo G halfPlane (extremalTarget p) ∧
    G 0 = (0 : ℂ) ∧ poleParam (extremalTarget p) 0 = p ∧
    ∀ n : ℕ, 2 ≤ n → derivativeRatio n G 0 (radius (planeDomain halfPlane) 0)
      (radius (extremalTarget p) 0) = D p 1 n := by sorry

end Goodman
end
end

section

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Goodman

theorem unweighted_cayley_properties {h : ℂ → ℂ} (hh : IsSchwarz h) {t : ℂ} (ht : ‖t‖ = 1) :
    let C := fun z : ℂ => (1+t*h z)/(1-t*h z)
    AnalyticOnNhd ℂ C disk ∧ C 0 = 1 ∧ ∀ z ∈ disk, 0 < (C z).re := by sorry

theorem slit_second_from_robertson (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {F : ℂ → ℂ} (hF : IsS F)
    {n : ℕ} (hn : 2 ≤ n) (he : ‖coeff n (fun z => (slitR p : ℂ)*F (q z))‖ = A p n) :
    coeff 2 F = 2 := by sorry

theorem composite_slit_deficit (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℂ → ℂ} (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f)
    {h e : ℂ → ℂ} (hh : IsSchwarz h) (he : IsWeight e) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => e z * finitePart (f (h z)))‖ ≤
      A p n - slitR p * (coeff n q).re * (1 - ‖e 0 * (deriv h 0)^n‖) := by sorry

theorem strict_inversion_disk {u : ℂ} (hu : 1 / 2 < u.re) : ‖1/u-1‖ < 1 := by sorry

theorem convex_binomial_expansion (n : ℕ) (v : ℂ → ℂ) (z : ℂ) :
    (1 + z*v z)^n = ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) * z^j * (v z)^j := by sorry

theorem equality_forces_unit_derivative (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {h : ℂ → ℂ} (hh : IsSchwarz h) {n : ℕ} (hn : 1 ≤ n)
    (heq : ‖coeff n (fun z => finitePart (f (h z)))‖ = A p n) : ‖deriv h 0‖ = 1 := by sorry

theorem centered_disk_bound (H1 : Robertson) {U : Set Sphere} {w : ℂ} (c : CenteredChart U w)
    {G : ℂ → Sphere} (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U) (hw : G 0 = (w : Sphere))
    {E : ℂ → ℂ} (hE : IsWeight E) {k : ℕ} (hk : 1 ≤ k) :
    ‖coeff k (fun z => E z * ((finitePart (G z) - w) / (radius U w : ℂ)))‖ ≤ A (poleParam U w) k := by sorry

end Goodman
end
end

