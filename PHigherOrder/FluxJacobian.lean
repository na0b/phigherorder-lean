import PHigherOrder.PFlux

/-- The Jacobian of the `p`-flux, i.e. the matrix the paper writes as
`D_xi A(xi) = |xi|^(p-2) (I + (p-2) xi ⊗ xi / |xi|^2)` (paper line 171), encoded as a
continuous linear map of the plane.

Concretely `FluxJacobian p ξ w = ‖ξ‖^(p-2) • (w + ((p-2)/‖ξ‖^2) * ⟪ξ, w⟫ • ξ)`, where
`‖ξ‖^(p-2)` is a real power and `ξ ⊗ ξ` is the rank-one map `w ↦ ⟪ξ, w⟫ • ξ`, realized as
`(innerSL ℝ ξ).smulRight ξ`.

At `ξ = 0` the expression degenerates (the Lean conventions `0^(p-2) = 0` for `p ≠ 2` and
`c / 0 = 0` make it the zero map); the definition is only ever used on an annulus
`0 < a ≤ ‖ξ‖ ≤ b` away from the origin, which is exactly where the paper uses it and where
`FluxJacobianElliptic` shows it really is the derivative of `PFlux p`. -/
noncomputable def FluxJacobian (p : ℝ) (ξ : Plane) : Plane →L[ℝ] Plane :=
  ‖ξ‖ ^ (p - 2) • (ContinuousLinearMap.id ℝ Plane
    + ((p - 2) / ‖ξ‖ ^ 2) • (innerSL ℝ ξ).smulRight ξ)
