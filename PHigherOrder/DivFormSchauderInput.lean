import PHigherOrder.IsLinearDivSol

/-- Interior Schauder estimates for uniformly elliptic linear equations in
divergence form with Holder coefficients, as a named hypothesis.  For every order
`j`, Holder exponent `κ ∈ (0,1)`, ellipticity bounds `0 < lam ≤ Lam`, coefficient
bound `M > 0` and radii `0 < r' < r`, there is a constant `C > 0`, depending on
those parameters only, such that every normalized weak solution `w` of
`div (A Dw) = 0` on `ball 0 r` whose coefficient field `A` is uniformly elliptic
with bounds `lam, Lam` and has `C^{j,κ}` norms bounded by `M` satisfies
`‖w‖_{C^{j+1,κ}(ball 0 r')} ≤ C`. -/
structure DivFormSchauderInput : Prop where
  schauder : ∀ (j : ℕ) (κ lam Lam M r r' : ℝ),
      0 < κ → κ < 1 → 0 < lam → lam ≤ Lam → 0 < M → 0 < r' → r' < r →
      ∃ C > 0, ∀ (A : Plane → (Plane →L[ℝ] Plane)) (w : Plane → ℝ) (G : Plane → Plane),
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ ξ : Plane,
            lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ ∧ ‖A x ξ‖ ≤ Lam * ‖ξ‖) →
        ContDiffOn ℝ (j : ℕ∞) A (Metric.ball 0 r) →
        (∀ i ≤ j, ∀ x ∈ Metric.ball (0 : Plane) r, ‖iteratedFDeriv ℝ i A x‖ ≤ M) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
            ‖iteratedFDeriv ℝ j A x - iteratedFDeriv ℝ j A y‖ ≤ M * ‖x - y‖ ^ κ) →
        IsLinearDivSol (Metric.ball 0 r) A w G →
        (∀ x ∈ Metric.ball (0 : Plane) r, |w x| ≤ 1) →
        ContDiffOn ℝ ((j + 1 : ℕ) : ℕ∞) w (Metric.ball 0 r') ∧
        (∀ i ≤ j + 1, ∀ x ∈ Metric.ball (0 : Plane) r', ‖iteratedFDeriv ℝ i w x‖ ≤ C) ∧
        (∀ x ∈ Metric.ball (0 : Plane) r', ∀ y ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ (j + 1) w x - iteratedFDeriv ℝ (j + 1) w y‖ ≤ C * ‖x - y‖ ^ κ)
