import PHigherOrder.IsPHarm

/-- The classical first-order estimates of Lewis and Tolksdorf (paper eq:first),
as a named bundle of data for `p`.  It carries an exponent `kappa ∈ (0,1)` and a
constant `C₀ > 0`, both depending only on `p`, together with the UNIFORM interior
`C^{1,kappa}` estimate they satisfy: every `p`-harmonic `v` on the unit ball with
`|v| ≤ 1` there is `C^1` on `ball 0 (3/4)`, with classical gradient bounded by `C₀`
and `kappa`-Holder with constant `C₀` on that ball. -/
structure FirstOrderEstimateInput (p : ℝ) where
  kappa : ℝ
  C₀ : ℝ
  kappa_pos : 0 < kappa
  kappa_lt_one : kappa < 1
  C₀_pos : 0 < C₀
  est : ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
      (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) →
      ContDiffOn ℝ 1 v (Metric.ball 0 (3 / 4)) ∧
      (∀ x ∈ Metric.ball (0 : Plane) (3 / 4), ‖gradient v x‖ ≤ C₀) ∧
      (∀ x ∈ Metric.ball (0 : Plane) (3 / 4), ∀ y ∈ Metric.ball (0 : Plane) (3 / 4),
        ‖gradient v x - gradient v y‖ ≤ C₀ * ‖x - y‖ ^ kappa)
