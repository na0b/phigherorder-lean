import PHigherOrder.Plane

/-- The `p`-flux `A_p(xi) = |xi|^(p-2) xi` of the `p`-Laplace operator
`-div (|Du|^(p-2) Du)`.  The exponent is a real power, and `A_p 0 = 0` for every
`p` because the scalar factor is multiplied by `xi` itself. -/
noncomputable def PFlux (p : ℝ) (ξ : Plane) : Plane :=
  ‖ξ‖ ^ (p - 2) • ξ
