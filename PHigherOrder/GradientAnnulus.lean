import PHigherOrder.FirstOrderEstimateInput

/-- The first step of the paper's proof of lem:noncritical (paper lines 166-170): a radius
`tau ∈ (0, 1/4)`, depending only on `p` and `delta` through the Lewis-Tolksdorf data
`kappa, C₀`, on whose doubled ball the gradient of every normalized `p`-harmonic function
with `|Dv(0)| > delta` is trapped in the annulus `delta/2 ≤ |Dv| ≤ C₀`.

The paper's choice is `C₀ (2 tau)^kappa ≤ delta/2`: the `kappa`-Holder estimate of
eq:first then moves `Dv` by at most `delta/2` across `ball 0 (2 tau)`, so it can neither
reach `0` nor leave the ball of radius `C₀`.

The third conjunct, `‖Dv x - Dv 0‖ ≤ delta/2`, records that displacement bound itself and is
what the Schauder bootstrap actually needs: it says the RANGE of `Dv` on `ball 0 (2 tau)` lies
in the closed ball of radius `delta/2` about `Dv 0`, a CONVEX set which avoids the origin
because `delta < ‖Dv 0‖`.  The annulus `delta/2 ≤ ‖xi‖ ≤ C₀` of the first two conjuncts is not
convex, so the mean value inequality cannot be applied along a segment joining two values of
`Dv` using it alone.

The quantifier order is the one the paper's uniformity requires and the one pm-0005 is
about: `tau` is produced BEFORE `v`, from `p` and `delta` alone. -/
theorem GradientAnnulus (p : ℝ) (F : FirstOrderEstimateInput p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) → δ < ‖gradient v 0‖ →
        ContDiffOn ℝ 1 v (Metric.ball 0 (2 * τ)) ∧
          ∀ x ∈ Metric.ball (0 : Plane) (2 * τ),
            δ / 2 ≤ ‖gradient v x‖ ∧ ‖gradient v x‖ ≤ F.C₀
              ∧ ‖gradient v x - gradient v 0‖ ≤ δ / 2 := by
  -- Choice of `τ`.  One threshold is wanted, not a `δ` for every `ε`, so solve for it:
  -- `s := δ / (2 * F.C₀)` and `τ := (1/2) * min (1/4) (s ^ (1 / F.kappa))`.
  obtain ⟨s, hsdef⟩ : ∃ t : ℝ, t = δ / (2 * F.C₀) := ⟨_, rfl⟩
  have hCne : F.C₀ ≠ 0 := ne_of_gt F.C₀_pos
  have hs0 : 0 < s := by
    rw [hsdef]
    exact div_pos hδ (by linarith [F.C₀_pos])
  obtain ⟨τ, hτdef⟩ : ∃ t : ℝ, t = 1 / 2 * min (1 / 4) (s ^ (1 / F.kappa)) := ⟨_, rfl⟩
  have hroot0 : 0 < s ^ (1 / F.kappa) := Real.rpow_pos_of_pos hs0 _
  have hτ0 : 0 < τ := by
    rw [hτdef]
    have : 0 < min (1 / 4 : ℝ) (s ^ (1 / F.kappa)) := lt_min (by norm_num) hroot0
    linarith
  have hτ8 : τ ≤ 1 / 8 := by
    rw [hτdef]
    have : min (1 / 4 : ℝ) (s ^ (1 / F.kappa)) ≤ 1 / 4 := min_le_left _ _
    linarith
  have h2τroot : 2 * τ ≤ s ^ (1 / F.kappa) := by
    rw [hτdef]
    have : min (1 / 4 : ℝ) (s ^ (1 / F.kappa)) ≤ s ^ (1 / F.kappa) := min_le_right _ _
    linarith
  -- `(s ^ (1 / κ)) ^ κ = s`, so `C₀ (2τ)^κ ≤ δ/2` -- the paper's choice.
  have hrootpow : (s ^ (1 / F.kappa)) ^ F.kappa = s := by
    rw [← Real.rpow_mul hs0.le, one_div_mul_cancel (ne_of_gt F.kappa_pos), Real.rpow_one]
  have hkey : F.C₀ * (2 * τ) ^ F.kappa ≤ δ / 2 := by
    have hmono : (2 * τ) ^ F.kappa ≤ s := by
      rw [← hrootpow]
      exact Real.rpow_le_rpow (by linarith) h2τroot F.kappa_pos.le
    have := mul_le_mul_of_nonneg_left hmono F.C₀_pos.le
    rw [hsdef] at this
    have hC : F.C₀ * (δ / (2 * F.C₀)) = δ / 2 := by
      field_simp
    rw [hC] at this
    exact this
  -- `τ` is now fixed, from `δ`, `F.kappa` and `F.C₀` alone.  Only now is `v` introduced,
  -- so the uniformity is structural rather than asserted.
  refine ⟨τ, hτ0, by linarith, ?_⟩
  intro v g hph hbd hgrad
  have hsub : Metric.ball (0 : Plane) (2 * τ) ⊆ Metric.ball (0 : Plane) (3 / 4) :=
    Metric.ball_subset_ball (by linarith)
  obtain ⟨hC1, hub, hhol⟩ := F.est v g hph hbd
  refine ⟨hC1.mono hsub, ?_⟩
  intro x hx
  have hx34 : x ∈ Metric.ball (0 : Plane) (3 / 4) := hsub hx
  have h034 : (0 : Plane) ∈ Metric.ball (0 : Plane) (3 / 4) :=
    Metric.mem_ball_self (by norm_num)
  have hxlt : ‖x‖ < 2 * τ := by
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact hx
  -- The displacement bound, which is the third conjunct and drives the other two.
  have hdisp : ‖gradient v x - gradient v 0‖ ≤ δ / 2 := by
    have h3 := hhol x hx34 0 h034
    rw [sub_zero] at h3
    have hpow : ‖x‖ ^ F.kappa ≤ (2 * τ) ^ F.kappa :=
      Real.rpow_le_rpow (norm_nonneg _) hxlt.le F.kappa_pos.le
    have := mul_le_mul_of_nonneg_left hpow F.C₀_pos.le
    linarith
  refine ⟨?_, hub x hx34, hdisp⟩
  -- Lower bound:  the displacement cannot carry `Dv x` down to `δ/2`.
  have htri := norm_sub_norm_le (gradient v 0) (gradient v x)
  rw [norm_sub_rev] at htri
  linarith
