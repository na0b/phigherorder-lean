import PHigherOrder.Approximation
import PHigherOrder.LocalBoundednessInput
import PHigherOrder.PHarmNormalize
import PHigherOrder.PHarmRestrict
import PHigherOrder.TaylorPolyAffine

/-- Paper eq:jet-bound and eq:jet-error (paper lines 283-303): the jets of a `p`-harmonic
`u ∈ L^p(B_1)` at any point of `B_{1/2}` are bounded by its `L^p` norm, and its degree-`k`
Taylor polynomial at that point approximates it to order `sigma = k + beta` on the quarter ball
around it.

Route, following the paper.  `LocalBoundednessInput` bounds `|u|` on `B_{3/4}` by
`C_b ‖u‖_{L^p(B_1)}`; the paper's normalizing constant is `M_0 = 2 C_b ‖u‖_{L^p(B_1)}`, and the
factor `2` is what makes `|w_x| ≤ 1` below come out, so it must not be dropped.  For
`x ∈ B_{1/2}` the rescaled function `w_x y = (u (x + y/4) - u x)/M_0` is `p`-harmonic on `B_1`
by `PHarmNormalize` with `r = 1/4`, `c = u x`, `M = M_0`, cut down by `PHarmRestrict`, vanishes
at `0`, and is bounded by `1` there; so `Approximation` applies, uniformly in `x` because its
constant is produced before the function.  `TaylorPolyAffine` then transports both conclusions
back: clause (1) at `r = 1/4` carries the factor `4^j ≤ 4^k` into the constant, and clause (2)
is literally the paper's `P_x(z) = u(x) + M_0 Q_x(4(z-x))`, so that
`u z - TaylorPoly k u x z = M_0 (w_x y - TaylorPoly k w_x 0 y)` at `y = 4 • (z - x)`, where
`‖y‖ = 4‖z - x‖ < 1` exactly when `z ∈ ball x (1/4)` — which is why `Approximation`'s error
clause had to be POINTWISE in the norm.

Both conclusions are stated in terms of `‖u‖_{L^p(B_1)}` rather than `M_0 = 2 C_b
‖u‖_{L^p(B_1)}`; the factor `2 C_b` depends only on `p` and is absorbed into `C`, which is the
paper's own bookkeeping ("all constants depend only on `p, k, beta`").  The case
`‖u‖_{L^p(B_1)} = 0`, i.e. `M_0 = 0`, is real and not vacuous, and is handled separately: `u`
then vanishes on `B_{3/4}` by local boundedness, so every jet of order `≥ 1` vanishes at `x` and
both sides of both conclusions are zero.

Everything is diagonal, and the full operator norm of `iteratedFDeriv ℝ j u x` is deliberately
never used. -/
theorem JetBounds (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        ∀ x ∈ Metric.ball (0 : Plane) (1 / 2),
          (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
              |iteratedFDeriv ℝ j u x (fun _ => w)|
                ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                      (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                  * ‖w‖ ^ j)
            ∧ (∀ z ∈ Metric.ball x (1 / 4),
                |u z - TaylorPoly k u x z|
                  ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                    * ‖z - x‖ ^ ((k : ℝ) + β)) := by
  -- Step 0: the constants, fixed before `u`
  obtain ⟨CA, hCA0, hCA⟩ := Approximation p hp hp2 hLR F hIM hsm hS k hk β hβ0 hβ1 hks
  obtain ⟨Cb, hCb0, hbound⟩ : ∃ cb : ℝ, 0 < cb ∧ ∀ (u : Plane → ℝ) (g : Plane → Plane),
      IsPHarm p (Metric.ball 0 1) u g → MeasureTheory.MemLp u (ENNReal.ofReal p)
        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
      ∀ x ∈ Metric.ball (0 : Plane) (3 / 4), |u x| ≤ cb * (MeasureTheory.eLpNorm u
        (ENNReal.ofReal p)
        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal :=
    ⟨hLB.Cb, hLB.Cb_pos, hLB.bound⟩
  have h4k0 : (0 : ℝ) < 4 ^ k := by positivity
  have h4s0 : (0 : ℝ) < (4 : ℝ) ^ ((k : ℝ) + β) := Real.rpow_pos_of_pos (by norm_num) _
  have hE1 : (0 : ℝ) < 2 * Cb * CA * 4 ^ k :=
    mul_pos (mul_pos (mul_pos two_pos hCb0) hCA0) h4k0
  have hE2 : (0 : ℝ) < 2 * Cb * CA * (4 : ℝ) ^ ((k : ℝ) + β) :=
    mul_pos (mul_pos (mul_pos two_pos hCb0) hCA0) h4s0
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ,
      t = max (2 * Cb * CA * 4 ^ k) (2 * Cb * CA * (4 : ℝ) ^ ((k : ℝ) + β)) := ⟨_, rfl⟩
  have hC1 : 2 * Cb * CA * 4 ^ k ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC2 : 2 * Cb * CA * (4 : ℝ) ^ ((k : ℝ) + β) ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨C, lt_of_lt_of_le hE1 hC1, ?_⟩
  intro u g hu hLp x hx
  set N := (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; exact ENNReal.toReal_nonneg
  have hxn : ‖x‖ < 1 / 2 := mem_ball_zero_iff.mp hx
  -- Step 1: local boundedness, and the inclusion `x + y/4 ∈ B_{3/4}` for `‖y‖ < 1`
  have hlb : ∀ ζ ∈ Metric.ball (0 : Plane) (3 / 4), |u ζ| ≤ Cb * N := hbound u g hu hLp
  have hx34 : x ∈ Metric.ball (0 : Plane) (3 / 4) := by
    rw [mem_ball_zero_iff]; linarith
  have hincl : ∀ y : Plane, ‖y‖ < 1 →
      x + (1 / 4 : ℝ) • y ∈ Metric.ball (0 : Plane) (3 / 4) := by
    intro y hy
    rw [mem_ball_zero_iff]
    have hs : ‖(1 / 4 : ℝ) • y‖ = (1 / 4 : ℝ) * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs]; norm_num
    calc ‖x + (1 / 4 : ℝ) • y‖ ≤ ‖x‖ + ‖(1 / 4 : ℝ) • y‖ := norm_add_le _ _
      _ = ‖x‖ + (1 / 4 : ℝ) * ‖y‖ := by rw [hs]
      _ < 3 / 4 := by linarith
  rcases eq_or_lt_of_le hN0 with hN | hN
  · -- Step 2: the case `N = 0`
    have hu0 : ∀ ζ ∈ Metric.ball (0 : Plane) (3 / 4), u ζ = 0 := by
      intro ζ hζ
      have h := hlb ζ hζ
      rw [← hN, mul_zero] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hev : u =ᶠ[nhds x] (fun _ : Plane => (0 : ℝ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx34] with ζ hζ using hu0 ζ hζ
    have hall : ∀ (j : ℕ) (v : Plane), iteratedFDeriv ℝ j u x (fun _ => v) = 0 := by
      intro j v
      rw [(hev.iteratedFDeriv ℝ j).self_of_nhds]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rw [iteratedFDeriv_zero_apply]
      · rw [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
        rfl
    refine ⟨fun j _ _ w => ?_, fun z hz => ?_⟩
    · rw [hall j w, abs_zero, ← hN, mul_zero, zero_mul]
    · have hz34 : z ∈ Metric.ball (0 : Plane) (3 / 4) := by
        rw [mem_ball_zero_iff]
        have hzx : ‖z - x‖ < 1 / 4 := by
          rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
        calc ‖z‖ = ‖z - x + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
          _ < 3 / 4 := by linarith
      have htp : TaylorPoly k u x z = 0 := by
        rw [TaylorPoly]
        refine Finset.sum_eq_zero ?_
        intro j _
        rw [hall j (z - x), mul_zero]
      rw [htp, hu0 z hz34, sub_zero, abs_zero, ← hN, mul_zero, zero_mul]
  · -- Step 3: the case `N > 0`
    obtain ⟨M0, hM0def⟩ : ∃ t : ℝ, t = 2 * Cb * N := ⟨_, rfl⟩
    have hM0 : 0 < M0 := by rw [hM0def]; exact mul_pos (mul_pos two_pos hCb0) hN
    have hM0ne : M0 ≠ 0 := ne_of_gt hM0
    -- (3a) the rescaled function
    obtain ⟨wx, hwx⟩ : ∃ f : Plane → ℝ,
        ∀ y : Plane, f y = (u (x + (1 / 4 : ℝ) • y) - u x) / M0 := ⟨_, fun _ => rfl⟩
    have hwxeq : wx = fun y : Plane => (u (x + (1 / 4 : ℝ) • y) - u x) / M0 := funext hwx
    have hsub : Metric.ball (0 : Plane) 1
        ⊆ {y : Plane | x + (1 / 4 : ℝ) • y ∈ Metric.ball 0 1} := by
      intro y hy
      simp only [Set.mem_ofPred_eq]
      exact Metric.ball_subset_ball (by norm_num) (hincl y (mem_ball_zero_iff.mp hy))
    have hphwx : IsPHarm p (Metric.ball 0 1) wx
        (fun y : Plane => ((1 / 4 : ℝ) / M0) • g (x + (1 / 4 : ℝ) • y)) := by
      rw [hwxeq]
      exact (PHarmRestrict p hp hp2 _ _ _
        (PHarmNormalize p hp hp2 (Metric.ball 0 1) u g x (1 / 4) M0 (u x)
          (by norm_num) hM0 hu)).1 (Metric.ball 0 1) Metric.isOpen_ball hsub
    have hwx0 : wx 0 = 0 := by
      rw [hwx 0, smul_zero, add_zero, sub_self, zero_div]
    have hwxb : ∀ y ∈ Metric.ball (0 : Plane) 1, |wx y| ≤ 1 := by
      intro y hy
      have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
      have h1 : |u (x + (1 / 4 : ℝ) • y)| ≤ Cb * N := hlb _ (hincl y hy1)
      have h2 : |u x| ≤ Cb * N := hlb x hx34
      rw [hwx y, abs_div, abs_of_pos hM0, div_le_one hM0, hM0def]
      calc |u (x + (1 / 4 : ℝ) • y) - u x|
          ≤ |u (x + (1 / 4 : ℝ) • y)| + |u x| := abs_sub _ _
        _ ≤ 2 * Cb * N := by linarith
    -- (3b) `Approximation` applies to `w_x`
    obtain ⟨hA1, hA2⟩ := hCA wx _ hphwx hwxb hwx0
    -- (3c) local `C^k` regularity of `u` at `x`
    obtain ⟨ρ, hρ0, Cρ, hCρ0, hballsub, hcd, hhold⟩ :=
      hIM.reg (Metric.ball 0 1) u g hu k β hβ0 hβ1 hks x
        (Metric.ball_subset_ball (by norm_num) hx34)
    -- (3d) transport
    obtain ⟨haff1, haff2⟩ :=
      TaylorPolyAffine k u x ρ hρ0 hcd (1 / 4) (by norm_num) M0 hM0 wx hwx
    refine ⟨fun j hj1 hjk w => ?_, fun z hz => ?_⟩
    · -- (3e) conclusion (1)
      have hsolve : iteratedFDeriv ℝ j u x (fun _ => w)
          = M0 * 4 ^ j * iteratedFDeriv ℝ j wx 0 (fun _ => w) := by
        rw [haff1 j hj1 hjk w]
        field_simp
        rw [mul_assoc, ← mul_pow]
        norm_num
      have h4j : (4 : ℝ) ^ j ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hjk
      have h4j0 : (0 : ℝ) < 4 ^ j := by positivity
      have hwbound : |iteratedFDeriv ℝ j wx 0 (fun _ => w)| ≤ CA * ‖w‖ ^ j := hA1 j hj1 hjk w
      have hwn : (0 : ℝ) ≤ ‖w‖ ^ j := by positivity
      rw [hsolve, abs_mul, abs_of_pos (mul_pos hM0 h4j0)]
      calc M0 * 4 ^ j * |iteratedFDeriv ℝ j wx 0 (fun _ => w)|
          ≤ M0 * 4 ^ j * (CA * ‖w‖ ^ j) :=
            mul_le_mul_of_nonneg_left hwbound (le_of_lt (mul_pos hM0 h4j0))
        _ ≤ M0 * 4 ^ k * (CA * ‖w‖ ^ j) := by
            have : M0 * 4 ^ j ≤ M0 * 4 ^ k := mul_le_mul_of_nonneg_left h4j (le_of_lt hM0)
            exact mul_le_mul_of_nonneg_right this (by positivity)
        _ = (2 * Cb * CA * 4 ^ k) * N * ‖w‖ ^ j := by rw [hM0def]; ring
        _ ≤ C * N * ‖w‖ ^ j := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hN0) hwn
    · -- (3f) conclusion (2)
      have hzx : ‖z - x‖ < 1 / 4 := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
      obtain ⟨y, hydef⟩ : ∃ v : Plane, v = (4 : ℝ) • (z - x) := ⟨_, rfl⟩
      have hyn : ‖y‖ = 4 * ‖z - x‖ := by
        rw [hydef, norm_smul, Real.norm_eq_abs]; norm_num
      have hy1 : ‖y‖ < 1 := by rw [hyn]; linarith
      have hxy : x + (1 / 4 : ℝ) • y = z := by
        rw [hydef, smul_smul]
        norm_num
      have hwxy : M0 * wx y = u z - u x := by
        rw [hwx y, hxy, mul_div_cancel₀ _ hM0ne]
      have haffz : TaylorPoly k u x z = u x + M0 * TaylorPoly k wx 0 y := by
        rw [haff2 z, hydef]
        norm_num
      have hdiff : u z - TaylorPoly k u x z = M0 * (wx y - TaylorPoly k wx 0 y) := by
        rw [haffz, mul_sub, hwxy]; ring
      have hAz : |wx y - TaylorPoly k wx 0 y| ≤ CA * ‖y‖ ^ ((k : ℝ) + β) := hA2 y hy1
      have hzxn : (0 : ℝ) ≤ ‖z - x‖ := norm_nonneg _
      have hpow : ‖y‖ ^ ((k : ℝ) + β)
          = (4 : ℝ) ^ ((k : ℝ) + β) * ‖z - x‖ ^ ((k : ℝ) + β) := by
        rw [hyn, Real.mul_rpow (by norm_num) hzxn]
      have hzxs : (0 : ℝ) ≤ ‖z - x‖ ^ ((k : ℝ) + β) := Real.rpow_nonneg hzxn _
      rw [hdiff, abs_mul, abs_of_pos hM0]
      calc M0 * |wx y - TaylorPoly k wx 0 y|
          ≤ M0 * (CA * ‖y‖ ^ ((k : ℝ) + β)) :=
            mul_le_mul_of_nonneg_left hAz (le_of_lt hM0)
        _ = (2 * Cb * CA * (4 : ℝ) ^ ((k : ℝ) + β)) * N * ‖z - x‖ ^ ((k : ℝ) + β) := by
            rw [hpow, hM0def]; ring
        _ ≤ C * N * ‖z - x‖ ^ ((k : ℝ) + β) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hN0) hzxs
