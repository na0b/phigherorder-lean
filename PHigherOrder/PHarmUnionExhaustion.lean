import PHigherOrder.IsPHarm
import PHigherOrder.PFluxContinuity
import PHigherOrder.VanishingOffTsupport
set_option linter.unusedVariables false

/-- Exhaustion: `p`-harmonicity on an increasing sequence of open sets, with one
and the same weak gradient, transfers to the union.

This is what assembles a family of ball-by-ball conclusions into one on a larger
domain.  A blow-up `u_r` is `p`-harmonic only on `ball 0 (ρ / r)`, never on
`Set.univ` for a fixed `r`, so a limit-passage lemma stated for a single fixed
domain can only be applied one ball at a time; this node turns the resulting family
of statements into `p`-harmonicity on the union.  The one substantive step is that a
compact subset of the union already lies in a single member, so a compactly
supported test function for the union is a test function for one member. -/
theorem PHarmUnionExhaustion (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (Ω : ℕ → Set Plane) (u : Plane → ℝ) (g : Plane → Plane)
    (hmono : Monotone Ω) (h : ∀ n : ℕ, IsPHarm p (Ω n) u g) :
    IsPHarm p (⋃ n, Ω n) u g := by
  have hopen : ∀ n : ℕ, IsOpen (Ω n) := fun n => (h n).openOmega
  have hUopen : IsOpen (⋃ n, Ω n) := isOpen_iUnion hopen
  have hUmeas : MeasurableSet (⋃ n, Ω n) := hUopen.measurableSet
  -- Step 1: a compact subset of the union already lies in a single member.
  have hstep1 : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K → ∃ N : ℕ, K ⊆ Ω N :=
    fun K hK hKc => hKc.elim_directed_cover Ω hopen hK hmono.directed_le
  obtain ⟨hval, hgrad⟩ := VanishingOffTsupport
  -- Step 2, condition (2): continuity on the union is pointwise, each member being open.
  have hcont : ContinuousOn u (⋃ n, Ω n) := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact (((h n).contU.continuousAt ((hopen n).mem_nhds hxn)).continuousWithinAt)
  -- Step 2, condition (3): countable-union criterion for a.e. strong measurability.
  have hmeas : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (⋃ n, Ω n)) :=
    MeasureTheory.AEStronglyMeasurable.iUnion fun n => (h n).measG
  -- Step 2, condition (4): local integrability via Step 1.
  have hloc : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖g x‖ ^ p) K := by
    intro K hK hKc
    obtain ⟨N, hN⟩ := hstep1 K hK hKc
    exact (h N).locIntG K hN hKc
  -- Step 4: conditions (5) and (6).  The test function's support sits in a single member,
  -- and every integrand vanishes off that support, so the union- and member-integrals agree.
  have hwg : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (⋃ n, Ω n) →
      ∫ x in (⋃ n, Ω n), u x • gradient φ x = - ∫ x in (⋃ n, Ω n), φ x • g x := by
    intro φ hφ hφc hφsub
    obtain ⟨N, hN⟩ := hstep1 (tsupport φ) hφsub hφc
    have hsub : Ω N ⊆ (⋃ n, Ω n) := Set.subset_iUnion Ω N
    have e1 : ∫ x in (⋃ n, Ω n), u x • gradient φ x = ∫ x in Ω N, u x • gradient φ x := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hsub ?_
      intro x hx
      rw [hgrad φ x fun hc => hx.2 (hN hc), smul_zero]
    have e2 : ∫ x in (⋃ n, Ω n), φ x • g x = ∫ x in Ω N, φ x • g x := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hsub ?_
      intro x hx
      rw [hval φ x fun hc => hx.2 (hN hc), zero_smul]
    rw [e1, e2]
    exact (h N).weakGrad φ hφ hφc hN
  have heqn : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (⋃ n, Ω n) →
      ∫ x in (⋃ n, Ω n), inner ℝ (PFlux p (g x)) (gradient φ x) = (0 : ℝ) := by
    intro φ hφ hφc hφsub
    obtain ⟨N, hN⟩ := hstep1 (tsupport φ) hφsub hφc
    have hsub : Ω N ⊆ (⋃ n, Ω n) := Set.subset_iUnion Ω N
    have e3 : ∫ x in (⋃ n, Ω n), inner ℝ (PFlux p (g x)) (gradient φ x)
        = ∫ x in Ω N, inner ℝ (PFlux p (g x)) (gradient φ x) := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hsub ?_
      intro x hx
      rw [hgrad φ x fun hc => hx.2 (hN hc), inner_zero_right]
    rw [e3]
    exact (h N).eqn φ hφ hφc hN
  exact ⟨hUopen, hcont, hmeas, hloc, hwg, heqn⟩
