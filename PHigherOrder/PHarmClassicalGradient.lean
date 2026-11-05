import PHigherOrder.Plane

/-- The classical gradient of a limit object, read off from the approximating
gradients.  If each `u n` has classical gradient `g n` at every point of an open
`Ω`, the `g n` converge to `G` uniformly on every compact subset of `Ω`, and
`u n → U` pointwise on `Ω`, then `U` has classical gradient `G x` at every `x ∈ Ω`;
in particular `gradient U = G` on `Ω`.

This is the bridge that lets a hypothesis about a CLASSICAL gradient — such as
`Du x₀ = 0` at a critical point — be read off a gradient produced by a limit.  Note
it needs no measure theory and no a.e. uniqueness of weak gradients: uniform
convergence of the derivatives identifies the limit derivative outright. -/
theorem PHarmClassicalGradient (Ω : Set Plane) (hΩ : IsOpen Ω)
    (u : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane) (U : Plane → ℝ) (G : Plane → Plane)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Ω, HasGradientAt (u n) (g n x) x)
    (hconv : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → TendstoUniformlyOn g G Filter.atTop K)
    (hptwise : ∀ x ∈ Ω, Filter.Tendsto (fun n => u n x) Filter.atTop (nhds (U x))) :
    ∀ x ∈ Ω, HasGradientAt U (G x) x ∧ gradient U x = G x := by
  -- Step 2: the Riesz map is a linear isometry, so the uniform convergence of the gradients
  -- transports verbatim to the Frechet derivatives -- same epsilon, same index.  On an open
  -- subset of the locally compact `Plane`, compact-by-compact uniform convergence IS locally
  -- uniform convergence.
  have hfd : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (y : Plane) => (InnerProductSpace.toDual ℝ Plane) (g n y))
      (fun y => (InnerProductSpace.toDual ℝ Plane) (G y)) Filter.atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro K hK hKc
    have h1 := hconv K hK hKc
    rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
    intro ε hε
    filter_upwards [h1 ε hε] with n hn y hy
    show dist ((InnerProductSpace.toDual ℝ Plane) (G y))
      ((InnerProductSpace.toDual ℝ Plane) (g n y)) < ε
    rw [dist_eq_norm, ← map_sub, (InnerProductSpace.toDual ℝ Plane).norm_map, ← dist_eq_norm]
    exact hn y hy
  -- Steps 1, 3 and 4:  the hypotheses in Frechet form, the limit theorem, and back.
  intro x hx
  have hU : HasFDerivAt U ((InnerProductSpace.toDual ℝ Plane) (G x)) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hfd
      (fun n y hy => hasGradientAt_iff_hasFDerivAt.mp (hderiv n y hy)) hptwise hx
  have hg : HasGradientAt U (G x) x := hasGradientAt_iff_hasFDerivAt.mpr hU
  exact ⟨hg, hg.gradient⟩
