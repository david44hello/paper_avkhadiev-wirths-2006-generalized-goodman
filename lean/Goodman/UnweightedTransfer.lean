-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.CoefficientComposition
public import Goodman.ReversedPolynomial
public import Goodman.SzapielMoments
public import Goodman.Transfer

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

/-- In degree zero the reversed polynomial is the constant one. -/
theorem szapiel_zero_multiplier (h : ℂ → ℂ) :
    (fun w : ℂ => ∑ j ∈ Finset.range (0+1), coeff 0 (fun z => h z^j) * w^(0-j)) =
      fun _ => 1 := by
  funext w
  simp [coeff]

/-- Szapiel's polynomial multiplier for unweighted subordination. The constant
term of the original moment polynomial vanishes in positive degree and gives the
constant multiplier one in degree zero. The same multiplier works for every germ. -/
theorem szapiel_unweighted_transfer {h : ℂ → ℂ} (hh : IsSchwarz h) (n : ℕ) :
    let P := fun w : ℂ => ∑ j ∈ Finset.range (n+1), coeff n (fun z => h z^j) * w^(n-j)
    IsWeight P ∧ P 0 = deriv h 0 ^ n ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 → coeff n (g ∘ h) = coeff n (fun w => P w * g w) := by
  let c (j : ℕ) := coeff n (fun z => h z^j)
  let P (w : ℂ) := ∑ j ∈ Finset.range (n+1), c j * w^(n-j)
  change IsWeight P ∧ P 0 = deriv h 0 ^ n ∧ _
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have hw : IsWeight P := by
    apply reversed_polynomial_weight
    intro t ht
    cases n with
    | zero => simp [c, coeff]
    | succ n => exact szapiel_moment_bound hh ht (Nat.succ_pos n)
  refine ⟨hw, ?_, ?_⟩
  · have hfirst := reversed_polynomial_coeff c (n := n) (j := n) le_rfl
    have hm := transfer_moment (e := fun _ => (1:ℂ)) analyticAt_const (hh.1 0 h0) hh.2.2 n n le_rfl
    have hconst : P 0 = c n := by simpa only [Nat.sub_self, coeff, iteratedDeriv_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, P] using hfirst
    exact hconst.trans (by simpa [c] using hm)
  · intro g hg
    rw [coeff_comp_finite hg (hh.1 0 h0) hh.2.2, transfer_coeff_product (hw.1 0 h0) hg]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact congrArg (fun a => coeff j g * a)
      (reversed_polynomial_coeff c (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm

end Goodman
