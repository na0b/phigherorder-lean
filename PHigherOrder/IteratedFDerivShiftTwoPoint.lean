import PHigherOrder.Plane

/-- THE ORDER SHIFT, TWO-POINT FORM: at any two points, the order-`(n+1)` jet difference of `f`
has the same norm as the order-`n` jet difference of `fderiv R f`.  Mathlib carries only the
one-point companion `norm_iteratedFDeriv_fderiv`; a Holder seminorm IS a two-point difference.
Arbitrary normed target, all points, no hypothesis on `f`: the shift is a linear isometry. -/
theorem IteratedFDerivShiftTwoPoint (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : Plane → Z) (n : ℕ) (x y : Plane) :
    ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖
      = ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
