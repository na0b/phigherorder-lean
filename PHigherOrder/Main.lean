import PHigherOrder.HolderFromJets
import PHigherOrder.JetBounds
import PHigherOrder.LocalBoundednessInput

/-- The paper's main theorem, `thm:main` (paper lines 108-113): for `1 < p < 2`, every integer
`k ≥ 2` and every `0 < beta < 1` with `k + beta < s(p)`, there is `C = C(p,k,beta) < ∞` such
that every `p`-harmonic `u ∈ L^p(B_1)` satisfies eq:main.

Two renderings separate this statement from eq:main as the paper writes it, and both are
discussed in the `.tex` statement, where the faithfulness argument belongs.  First, the
derivative terms are carried through DIAGONAL evaluations `D^j u(x)[w,…,w]`, homogeneous of
degree `j` in `w`, rather than through the operator norms `‖D^j u(x)‖`; that is the standing
interface of this development and it is forced by what Mathlib supplies.  Second, eq:main is
ONE inequality on a SUM of `k + 2` terms whereas the conclusion here is a conjunction of two
quantified FAMILIES of bounds; the two are interderivable with a factor depending only on `k`.
Both factors depend only on `k` and are absorbed by `C`, which the paper itself quantifies as
`C(p,k,beta)` at line 313.

The `j = 0` term of the paper's sum is the `L^∞` bound on `B_{1/2}` and needs no clause of its
own: at `j = 0` the diagonal evaluation is `u x` and `‖w‖ ^ 0 = 1`, so that case of the first
clause IS local boundedness, restricted from `B_{3/4}` to `B_{1/2}`, which is the ingredient
paper line 313 names alongside the derivative bounds.

`C` is produced BEFORE `u`, as a single maximum of the two suppliers' constants and the local
boundedness constant.  That quantifier order is the whole content of the theorem: it is the
uniformity the qualitative higher regularity of Iwaniec-Manfredi does not provide, and which
the compactness argument of section 2 is what supplies. -/
theorem Main (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        (∀ j : ℕ, j ≤ k → ∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ w : Plane,
            |iteratedFDeriv ℝ j u x (fun _ => w)|
              ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                * ‖w‖ ^ j)
          ∧ (∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
              ∀ w : Plane,
                |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
                  ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                    * ‖x - y‖ ^ β * ‖w‖ ^ k) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := JetBounds p hp hp2 hLR F hIM hsm hS hLB k hk β hβ0 hβ1 hks
  obtain ⟨C₂, hC₂pos, hC₂⟩ := HolderFromJets p hp hp2 hLR F hIM hsm hS hLB k hk β hβ0 hβ1 hks
  refine ⟨max C₁ (max C₂ hLB.Cb), lt_of_lt_of_le hC₁pos (le_max_left _ _), ?_⟩
  intro u g hph hLp
  have hN : (0:ℝ) ≤ (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
      (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal :=
    ENNReal.toReal_nonneg
  refine ⟨?_, ?_⟩
  · intro j hjk x hx w
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      have hx34 : x ∈ Metric.ball (0 : Plane) (3 / 4) :=
        Metric.mem_ball.mpr (by have := Metric.mem_ball.mp hx; linarith)
      have hb := hLB.bound u g hph hLp x hx34
      have hz : |iteratedFDeriv ℝ 0 u x (fun _ => w)| = |u x| := by
        simp [iteratedFDeriv_zero_apply]
      rw [hz, pow_zero, mul_one]
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ hN)
      exact (le_max_right C₂ hLB.Cb).trans (le_max_right C₁ _)
    · refine ((hC₁ u g hph hLp x hx).1 j hj1 hjk w).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hN) (by positivity)
  · intro x hx y hy w
    refine (hC₂ u g hph hLp x hx y hy w).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          ((le_max_left C₂ hLB.Cb).trans (le_max_right C₁ _)) hN)
        (Real.rpow_nonneg (norm_nonneg _) _))
      (by positivity)
