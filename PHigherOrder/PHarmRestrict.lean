import PHigherOrder.IsPHarm
import PHigherOrder.PFluxContinuity
import PHigherOrder.VanishingOffTsupport
set_option linter.unusedVariables false

/-- Domain restriction and data congruence for `p`-harmonicity.  If `u` is
`p`-harmonic on `Ω` with weak gradient `g`, then

* (a) `u` is `p`-harmonic with the same weak gradient on every open `Ω' ⊆ Ω`, and
* (b) `IsPHarm p Ω u g` depends on `u` and `g` only through their restrictions to
  `Ω`: replacing them by any `u'`, `g'` agreeing with them on `Ω` preserves it.

Neither is automatic: `IsPHarm` bundles the domain with an explicit weak gradient,
so it has no domain functoriality for free.  (a) is what feeds a solution on
`ball 0 1` into a statement about `ball 0 (1/2)`; (b) is what licenses extending a
limit object defined only on a closed ball by `0` off that ball. -/
theorem PHarmRestrict (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (Ω : Set Plane)
    (u : Plane → ℝ) (g : Plane → Plane) (h : IsPHarm p Ω u g) :
    (∀ Ω' : Set Plane, IsOpen Ω' → Ω' ⊆ Ω → IsPHarm p Ω' u g) ∧
    (∀ (u' : Plane → ℝ) (g' : Plane → Plane),
      Set.EqOn u u' Ω → Set.EqOn g g' Ω → IsPHarm p Ω u' g') := by
  have hOmeas : MeasurableSet Ω := h.openOmega.measurableSet
  obtain ⟨hval, hgrad⟩ := VanishingOffTsupport
  refine ⟨?_, ?_⟩
  · -- Part (a): restriction to an open subset.
    intro Ω' hopen hsub
    have hcont : ContinuousOn u Ω' := h.contU.mono hsub
    have hmeas : MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.volume.restrict Ω') :=
      h.measG.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hsub)
    have hloc : ∀ K : Set Plane, K ⊆ Ω' → IsCompact K →
        MeasureTheory.IntegrableOn (fun x => ‖g x‖ ^ p) K :=
      fun K hK hKc => h.locIntG K (hK.trans hsub) hKc
    have hwg : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ω' →
        ∫ x in Ω', u x • gradient φ x = - ∫ x in Ω', φ x • g x := by
      intro φ hφ hφc hφsub
      have e1 : ∫ x in Ω, u x • gradient φ x = ∫ x in Ω', u x • gradient φ x := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOmeas hsub ?_
        intro x hx
        rw [hgrad φ x fun hc => hx.2 (hφsub hc), smul_zero]
      have e2 : ∫ x in Ω, φ x • g x = ∫ x in Ω', φ x • g x := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOmeas hsub ?_
        intro x hx
        rw [hval φ x fun hc => hx.2 (hφsub hc), zero_smul]
      rw [← e1, ← e2]
      exact h.weakGrad φ hφ hφc (hφsub.trans hsub)
    have heq : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ω' →
        ∫ x in Ω', inner ℝ (PFlux p (g x)) (gradient φ x) = (0 : ℝ) := by
      intro φ hφ hφc hφsub
      have e3 : ∫ x in Ω, inner ℝ (PFlux p (g x)) (gradient φ x)
          = ∫ x in Ω', inner ℝ (PFlux p (g x)) (gradient φ x) := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOmeas hsub ?_
        intro x hx
        rw [hgrad φ x fun hc => hx.2 (hφsub hc), inner_zero_right]
      rw [← e3]
      exact h.eqn φ hφ hφc (hφsub.trans hsub)
    exact ⟨hopen, hcont, hmeas, hloc, hwg, heq⟩
  · -- Part (b): congruence of the data on Ω.
    intro u' g' hu hg
    have hgae : g =ᵐ[MeasureTheory.volume.restrict Ω] g' := by
      filter_upwards [MeasureTheory.ae_restrict_mem hOmeas] with x hx using hg hx
    have hcont : ContinuousOn u' Ω := h.contU.congr hu.symm
    have hmeas : MeasureTheory.AEStronglyMeasurable g'
        (MeasureTheory.volume.restrict Ω) := h.measG.congr hgae
    have hloc : ∀ K : Set Plane, K ⊆ Ω → IsCompact K →
        MeasureTheory.IntegrableOn (fun x => ‖g' x‖ ^ p) K := by
      intro K hK hKc
      refine (h.locIntG K hK hKc).congr_fun ?_ hKc.measurableSet
      intro x hx
      simp only [hg (hK hx)]
    have hwg : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ω →
        ∫ x in Ω, u' x • gradient φ x = - ∫ x in Ω, φ x • g' x := by
      intro φ hφ hφc hφsub
      have e1 : ∫ x in Ω, u' x • gradient φ x = ∫ x in Ω, u x • gradient φ x := by
        refine MeasureTheory.setIntegral_congr_fun hOmeas ?_
        intro x hx
        simp only [hu hx]
      have e2 : ∫ x in Ω, φ x • g' x = ∫ x in Ω, φ x • g x := by
        refine MeasureTheory.setIntegral_congr_fun hOmeas ?_
        intro x hx
        simp only [hg hx]
      rw [e1, e2]
      exact h.weakGrad φ hφ hφc hφsub
    have heq : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ω →
        ∫ x in Ω, inner ℝ (PFlux p (g' x)) (gradient φ x) = (0 : ℝ) := by
      intro φ hφ hφc hφsub
      have e3 : ∫ x in Ω, inner ℝ (PFlux p (g' x)) (gradient φ x)
          = ∫ x in Ω, inner ℝ (PFlux p (g x)) (gradient φ x) := by
        refine MeasureTheory.setIntegral_congr_fun hOmeas ?_
        intro x hx
        simp only [hg hx]
      rw [e3]
      exact h.eqn φ hφ hφc hφsub
    exact ⟨h.openOmega, hcont, hmeas, hloc, hwg, heq⟩
