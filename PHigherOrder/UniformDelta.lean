import PHigherOrder.Plane

/-- Uniform separation from the zero set of a continuous nonnegative functional on
a compact set.  If `F` is continuous and nonnegative on a compact `K` and `U` is an
open set containing the zero set `{z ∈ K | F z = 0}`, then some whole sublevel set
`{z ∈ K | F z ≤ δ}` with `δ > 0` is already contained in `U`.

This is the compactness step the paper uses to turn a cover of the critical members
of its family into a bound on the size of the gradient at the origin: the paper
argues it by contradiction through a convergent subsequence, and the direct form
here is that `F` attains a positive minimum on the compact set `K \ U`. -/
theorem UniformDelta (X : Type) [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (F : X → ℝ)
    (hF : ContinuousOn F K) (hFnn : ∀ z ∈ K, 0 ≤ F z)
    (U : Set X) (hU : IsOpen U) (hsub : {z ∈ K | F z = 0} ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ {z ∈ K | F z ≤ δ} ⊆ U := by
  by_cases hempty : (K \ U) = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro z hz
    by_contra hzU
    exact Set.notMem_empty z (hempty ▸ (show z ∈ K \ U from ⟨hz.1, hzU⟩))
  · have hcomp : IsCompact (K \ U) := hK.diff hU
    have hne : (K \ U).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨z₀, hz₀, hmin⟩ := hcomp.exists_isMinOn hne (hF.mono Set.sdiff_subset)
    have hpos : 0 < F z₀ := by
      rcases lt_or_eq_of_le (hFnn z₀ hz₀.1) with h | h
      · exact h
      · exact absurd (hsub ⟨hz₀.1, h.symm⟩) hz₀.2
    refine ⟨F z₀ / 2, by positivity, ?_⟩
    intro z hz
    by_contra hzU
    have hle : F z₀ ≤ F z := hmin ⟨hz.1, hzU⟩
    have hz2 : F z ≤ F z₀ / 2 := hz.2
    linarith
