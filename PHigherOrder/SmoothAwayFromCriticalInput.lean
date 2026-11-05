import PHigherOrder.IsPHarm

/-- Smoothness of `p`-harmonic functions away from their critical points, as a
named hypothesis on `p`:  if `u` is `p`-harmonic on `Ω` and `U ⊆ Ω` is an open set
on which `u` is `C^1` with nowhere-vanishing classical gradient, then `u` is `C^∞`
on `U`. -/
structure SmoothAwayFromCriticalInput (p : ℝ) : Prop where
  smooth : ∀ (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
      IsPHarm p Ω u g → ∀ U : Set Plane, IsOpen U → U ⊆ Ω →
      ContDiffOn ℝ 1 u U → (∀ x ∈ U, gradient u x ≠ 0) →
      ContDiffOn ℝ (⊤ : ℕ∞) u U
