import PHigherOrder.CoeffFieldBounds
import PHigherOrder.GradientFieldOrderShift

/-- The coefficient field `Phi . Dv` is `C^{j,kappa}` as soon as the SCALAR function `v` carries
`C^{j+1,kappa}` bounds.

`CoeffFieldBounds` takes its hypotheses on the `Plane`-valued map `H` it composes with, but the
Schauder bootstrap of the paper's lem:noncritical carries its inductive hypothesis on the scalar
solution `v`, and applies the composition estimate with `H := Dv`, the CLASSICAL GRADIENT FIELD.
This node performs that conversion and then the composition estimate, so the bootstrap can quote
one node for the whole of its step "the coefficient field is `C^{i,kappa}`".

The conversion is at NO loss of constant: `D^{n}(Dv)(x)` and `D^{n+1}v(x)` differ by a fixed
linear isometry, namely the Riesz map post-composed into the `n`-linear maps and then the
order-shift isometry, so their norms agree and so do the norms of their two-point differences.
That the Riesz map must be inserted at all is the whole content of the conversion: the order-shift
proposition differentiates the Frechet derivative `Df : Plane -> L(Plane, R)`, which takes values
in the dual of the plane, whereas the classical gradient field `Dv : Plane -> Plane` takes values
in the plane itself, and this development keeps the two apart.

As in `CoeffFieldBounds`, the constant `M` is quantified BEFORE `U`, `V`, `Phi` and `v`, which is
what lets the bootstrap fix all of its constants before any solution is given. -/
theorem CoeffFieldFromScalarBounds (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C D d : ℝ) (hC : 0 < C) (hD : 0 < D) (hd : 0 < d) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (U V : Set Plane) (Φ : Plane → W) (v : Plane → ℝ),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        IsOpen V → Convex ℝ V → (∀ x ∈ U, gradient v x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) Φ V →
        (∀ i ≤ j + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i Φ ξ‖ ≤ C) →
        ContDiffOn ℝ (⊤ : ℕ∞) v U →
        (∀ i ≤ j + 1, ∀ x ∈ U, ‖iteratedFDeriv ℝ i v x‖ ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ (j + 1) v x - iteratedFDeriv ℝ (j + 1) v y‖ ≤ D * ‖x - y‖ ^ κ) →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (Φ ∘ gradient v) x‖ ≤ M)
          ∧ (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ j (Φ ∘ gradient v) x - iteratedFDeriv ℝ j (Φ ∘ gradient v) y‖
                ≤ M * ‖x - y‖ ^ κ) := by
  obtain ⟨M, hM, hCFB⟩ := CoeffFieldBounds W j κ hκ0 hκ1 C D d hC hD hd
  refine ⟨M, hM, ?_⟩
  intro U V Φ v hUo hUc hUd hVo hVc hHV hΦ hΦb hv hvb hvh
  -- The Riesz factorization of the gradient field, its smoothness, and the two sharp
  -- order-shift bridges, at a point and at a pair of points of `U`, all at no loss of
  -- constant: the conversion is an equality, not an estimate.
  obtain ⟨-, hgC, hbrSup, hbrHol⟩ := GradientFieldOrderShift U v hUo hv
  -- The composition estimate, with the converted hypotheses.
  refine hCFB U V Φ (gradient v) hUo hUc hUd hVo hVc hHV hΦ hΦb hgC ?_ ?_
  · intro i hi x hx
    rw [hbrSup i x]
    exact hvb (i + 1) (by omega) x hx
  · intro x hx y hy
    rw [hbrHol j x hx y hy]
    exact hvh x hx y hy
