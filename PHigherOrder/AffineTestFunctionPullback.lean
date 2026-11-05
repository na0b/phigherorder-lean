import PHigherOrder.Plane

/-- THE TEST-FUNCTION CORRESPONDENCE UNDER AN AFFINE SUBSTITUTION.  Write `T x = x₀ + r • x` for
the affine dilation and `S y = r⁻¹ • (y - x₀)` for its inverse, `r > 0`.  If `φ` is a test
function admissible for the PULLED-BACK domain `T⁻¹ Ω = {x | x₀ + r • x ∈ Ω}` -- smooth, compactly
supported, with `tsupport φ` inside that set -- then its pushforward `ψ := φ ∘ S` is a test
function admissible for `Ω` itself, and the two gradients are related by the chain rule

`gradient φ x = r • gradient ψ (x₀ + r • x)`   for every `x`.

Four conclusions, because a test function is four things at once: smoothness, compact support,
support inside the domain, and -- for a weak formulation -- a known gradient.  All four are
needed together, which is why they are one lemma: a weak equation on the rescaled domain is
tested against `φ` and must be matched against the original equation tested against `ψ`, so
every clause is consumed at the same moment.

The support clause is where the substitution does real work.  `tsupport ψ` is contained in
`S⁻¹(tsupport φ)`, which equals the IMAGE `T(tsupport φ)` because `T` and `S` are mutually
inverse; compactness then transfers along the continuous `T`, and membership in `Ω` follows from
`tsupport φ ⊆ T⁻¹ Ω` after cancelling `T ∘ S`.  The factor `r` in the gradient clause, rather
than `r⁻¹`, is likewise forced: `DS = r⁻¹ I`, so the chain rule puts `r⁻¹` on the pushforward's
gradient and `r` appears when that is solved for the original.

No hypothesis on `Ω` is needed -- not even openness.  The statement is about supports and the
chain rule, both of which are insensitive to it. -/
theorem AffineTestFunctionPullback (x₀ : Plane) (r : ℝ) (hr : 0 < r) (Ω : Set Plane) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ {x : Plane | x₀ + r • x ∈ Ω} →
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane => φ (r⁻¹ • (y - x₀)))
      ∧ HasCompactSupport (fun y : Plane => φ (r⁻¹ • (y - x₀)))
      ∧ tsupport (fun y : Plane => φ (r⁻¹ • (y - x₀))) ⊆ Ω
      ∧ (∀ x : Plane, gradient φ x
          = r • gradient (fun y : Plane => φ (r⁻¹ • (y - x₀))) (x₀ + r • x)) := by
  -- `T` and `S` are mutually inverse affine homeomorphisms.
  have hrne : r ≠ 0 := ne_of_gt hr
  have hST : ∀ x : Plane, r⁻¹ • ((x₀ + r • x) - x₀) = x := by
    intro x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hrne, one_smul]
  have hTS : ∀ y : Plane, x₀ + r • (r⁻¹ • (y - x₀)) = y := by
    intro y
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
    abel
  have hTcont : Continuous (fun x : Plane => x₀ + r • x) := by fun_prop
  have hScont : Continuous (fun y : Plane => r⁻¹ • (y - x₀)) := by fun_prop
  intro φ hφ hφc hφsub
  have hSC : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane => r⁻¹ • (y - x₀)) :=
    ContDiff.const_smul _ (contDiff_id.sub contDiff_const)
  have himg : (fun y : Plane => r⁻¹ • (y - x₀)) ⁻¹' (tsupport φ)
      = (fun x : Plane => x₀ + r • x) '' (tsupport φ) := by
    ext y
    constructor
    · intro hy
      exact ⟨r⁻¹ • (y - x₀), hy, hTS y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, hST x] using hx
  have hts : tsupport (fun y : Plane => φ (r⁻¹ • (y - x₀)))
      ⊆ (fun y : Plane => r⁻¹ • (y - x₀)) ⁻¹' (tsupport φ) := by
    have hsupp : Function.support (fun y : Plane => φ (r⁻¹ • (y - x₀)))
        = (fun y : Plane => r⁻¹ • (y - x₀)) ⁻¹' Function.support φ := rfl
    show closure (Function.support (fun y : Plane => φ (r⁻¹ • (y - x₀)))) ⊆ _
    rw [hsupp]
    exact hScont.closure_preimage_subset _
  refine ⟨hφ.comp hSC, ?_, ?_, ?_⟩
  · have hc2 : IsCompact ((fun y : Plane => r⁻¹ • (y - x₀)) ⁻¹' (tsupport φ)) := by
      rw [himg]; exact hφc.image hTcont
    exact IsCompact.of_isClosed_subset hc2 isClosed_closure hts
  · intro y hy
    have h3 : x₀ + r • (r⁻¹ • (y - x₀)) ∈ Ω := hφsub (hts hy)
    rwa [hTS y] at h3
  · intro x
    have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hSd : HasFDerivAt (fun y : Plane => r⁻¹ • (y - x₀))
        (r⁻¹ • ContinuousLinearMap.id ℝ Plane) (x₀ + r • x) :=
      ((hasFDerivAt_id (x₀ + r • x)).sub_const x₀).const_smul r⁻¹
    have hφd : HasFDerivAt φ (fderiv ℝ φ x) (r⁻¹ • ((x₀ + r • x) - x₀)) := by
      rw [hST x]; exact (hφdiff x).hasFDerivAt
    have hcomp : HasFDerivAt (fun y : Plane => φ (r⁻¹ • (y - x₀)))
        ((fderiv ℝ φ x).comp (r⁻¹ • ContinuousLinearMap.id ℝ Plane)) (x₀ + r • x) :=
      hφd.comp (x₀ + r • x) hSd
    have hfd : fderiv ℝ (fun y : Plane => φ (r⁻¹ • (y - x₀))) (x₀ + r • x)
        = r⁻¹ • fderiv ℝ φ x := by
      rw [hcomp.fderiv]
      ext z
      simp
    refine (InnerProductSpace.toDual ℝ Plane).injective ?_
    rw [toDual_gradient, map_smul, toDual_gradient, hfd, smul_smul,
      mul_inv_cancel₀ hrne, one_smul]
