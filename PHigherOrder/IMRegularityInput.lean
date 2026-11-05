import PHigherOrder.IsPHarm
import PHigherOrder.SOpt

/-- Iwaniec-Manfredi optimal qualitative regularity, as a named hypothesis on `p`,
in the local Holder form the paper uses:  for every `p`-harmonic `u` on a domain
`Ω`, every `k : ℕ` and every `0 < β < 1` with `k + β < SOpt p`, and every point
`x₀ ∈ Ω`, there are a radius `r > 0` and a constant `C > 0` such that `u` is `C^k`
on `ball x₀ r ⊆ Ω` and its `k`-th derivative is `β`-Holder there with constant `C`.

The regularity is QUALITATIVE: `r` and `C` are quantified inside `∀ u g`, so they
are allowed to depend on the solution.  That non-uniformity is the entire reason the
paper needs a compactness argument. -/
structure IMRegularityInput (p : ℝ) : Prop where
  reg : ∀ (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
      IsPHarm p Ω u g →
      ∀ (k : ℕ) (β : ℝ), 0 < β → β < 1 → (k : ℝ) + β < SOpt p →
      ∀ x₀ ∈ Ω, ∃ r > 0, ∃ C > 0, Metric.ball x₀ r ⊆ Ω ∧
        ContDiffOn ℝ (k : ℕ∞) u (Metric.ball x₀ r) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball x₀ r,
          ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k u y‖ ≤ C * ‖x - y‖ ^ β
