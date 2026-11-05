import PHigherOrder.FluxJacobian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-- THE FLUX JACOBIAN REALLY IS THE DERIVATIVE OF THE FLUX, away from the origin: for every
`p : ℝ` and every `ξ ≠ 0`, the `p`-flux `A_p` is Frechet differentiable at `ξ` with

`D A_p(ξ) = FluxJacobian p ξ`.

This is the definitional link between the two definition nodes `PFlux` and `FluxJacobian`.  They
are declared independently -- the second is a formula for a continuous linear map, not derived
from the first -- so the statement that one is the derivative of the other is a theorem and
everything downstream rests on it: the coefficient field of the differentiated equation IS
`D_ξ A_p` composed with the gradient, and that reading is only legitimate once this is proved.

No restriction on `p` is needed, and none is taken.  The lemma holds for every real `p`; the
hypothesis `1 < p < 2` that the rest of the development carries is about ellipticity constants
and plays no part here, which is why this clause is the one that mentions neither radius of an
annulus.

The route is through the SQUARED norm rather than the norm.  `ζ ↦ ‖ζ‖` is not differentiable at
the origin and its derivative elsewhere is awkward, whereas `ζ ↦ ‖ζ‖^2` is smooth everywhere
with derivative `2 innerSL ℝ ζ` given explicitly by the library.  Writing the flux as
`A_p(ζ) = (‖ζ‖^2)^((p-2)/2) ζ` -- an identity valid at EVERY `ζ`, the origin included -- turns
the computation into the real power rule composed with that derivative, times the identity, and
the product rule then assembles exactly the two summands of `FluxJacobian`. -/
theorem FluxJacobianIsDeriv (p : ℝ) :
    ∀ ξ : Plane, ξ ≠ 0 → HasFDerivAt (PFlux p) (FluxJacobian p ξ) ξ := by
  have hiSL : ∀ x y : Plane, (innerSL ℝ x) y = inner ℝ x y := fun _ _ => rfl
  -- The square-root-free form of the scalar factor.  Holds for EVERY `ζ`, including `0`.
  have hsqrpow : ∀ ζ : Plane, (‖ζ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) = ‖ζ‖ ^ (p - 2) := by
    intro ζ
    rw [← Real.rpow_natCast ‖ζ‖ 2, ← Real.rpow_mul (norm_nonneg ζ)]
    congr 1
    push_cast
    ring
  have hPF : ∀ ζ : Plane, PFlux p ζ = (‖ζ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) • ζ := by
    intro ζ
    rw [PFlux, hsqrpow]
  intro ξ hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hn2 : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  have hn2ne : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt hn2
  have hsq : HasFDerivAt (fun ζ : Plane => ‖ζ‖ ^ 2) ((2 : ℝ) • innerSL ℝ ξ) ξ := by
    have hd : DifferentiableAt ℝ (fun ζ : Plane => ‖ζ‖ ^ 2) ξ :=
      ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero) ξ
    have h := hd.hasFDerivAt
    rw [fderiv_norm_sq_apply] at h
    rw [two_smul ℝ (innerSL ℝ ξ)]
    rw [two_smul] at h
    exact h
  have hq : HasDerivAt (fun t : ℝ => t ^ ((p - 2) / 2))
      ((p - 2) / 2 * (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2 - 1)) (‖ξ‖ ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl hn2ne)
  have hprod := (hq.comp_hasFDerivAt ξ hsq).smul (hasFDerivAt_id ξ)
  have hfun : (((fun t : ℝ => t ^ ((p - 2) / 2)) ∘ fun ζ : Plane => ‖ζ‖ ^ 2) •
      (id : Plane → Plane)) = PFlux p := by
    funext ζ
    show (‖ζ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) • ζ = PFlux p ζ
    rw [hPF ζ]
  rw [hfun] at hprod
  have hsplit : (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2 - 1)
      = (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) / (‖ξ‖ ^ 2 : ℝ) := by
    rw [Real.rpow_sub hn2, Real.rpow_one]
  have hder : ((‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2)) • (ContinuousLinearMap.id ℝ Plane)
      + (((p - 2) / 2 * (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2 - 1)) •
          ((2 : ℝ) • innerSL ℝ ξ)).smulRight ξ
      = FluxJacobian p ξ := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [FluxJacobian, add_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, hiSL, smul_smul]
    rw [hsplit, hsqrpow ξ]
    have hc : (p - 2) / 2 * (‖ξ‖ ^ (p - 2) / ‖ξ‖ ^ 2) * 2 * (inner ℝ ξ w : ℝ)
        = ‖ξ‖ ^ (p - 2) * ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) := by
      field_simp
      try ring
    rw [smul_add, smul_smul, hc]
  rw [← hder]
  exact hprod
