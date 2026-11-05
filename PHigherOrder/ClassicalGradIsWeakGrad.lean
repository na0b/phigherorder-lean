import PHigherOrder.TestFunctionGradientIntegral
import PHigherOrder.VanishingOffTsupport

/-- On an open set, the CLASSICAL gradient of a `C^1` function is its DISTRIBUTIONAL gradient:
for every test function `φ` supported in `U`,
`∫_U w • gradient φ = - ∫_U φ • gradient w`.

This is the integration-by-parts identity that every weak formulation in the paper rests on,
and it is exactly the `weakGrad` field of `IsLinearDivSol` and of `IsPHarm` once the weak
gradient is taken to be the classical one.  Stated for a merely `C^1` function on an open set,
which is all any consumer needs and all the proof uses.

The proof multiplies `w` by the test function and applies `TestFunctionGradientIntegral` to the
product.  The product is `C^1` on all of the plane rather than only on `U` because `tsupport φ`
is a closed set contained in `U`, so `U` and the complement of `tsupport φ` are two open sets
covering the plane on each of which the product is `C^1` -- on the second it vanishes
identically.  That gluing is why the hypothesis `tsupport φ ⊆ U` cannot be weakened to
`Function.support φ ⊆ U`. -/
theorem ClassicalGradIsWeakGrad (U : Set Plane) (hU : IsOpen U) (w : Plane → ℝ)
    (hw : ContDiffOn ℝ 1 w U) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, w x • gradient φ x = - ∫ x in U, φ x • gradient w x := by
  intro φ hφ hsupp hts
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hKc : IsCompact (tsupport φ) := hsupp
  have hKcl : IsClosed (tsupport φ) := isClosed_tsupport φ
  -- `w` and its gradient are continuous on `U`;  `φ` and its gradient everywhere.
  have hwc : ContinuousOn w U := hw.continuousOn
  have hGc : ContinuousOn (gradient w) U :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hw.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hdφc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hφ1.continuous_fderiv one_ne_zero)
  -- Vanishing off the support.
  obtain ⟨hval0, hgrad0⟩ := VanishingOffTsupport
  -- The Riesz identification, used to carry the product rule from `fderiv` to `gradient`.
  have hgr : ∀ (f : Plane → ℝ) (x : Plane),
      gradient f x = (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ f x) := by
    intro f x
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  -- Step 1:  the product `h = φ w`, glued to a `C^1` function on the whole plane.
  obtain ⟨h, hhdef⟩ : ∃ f : Plane → ℝ, f = fun x => φ x * w x := ⟨_, rfl⟩
  have hh0 : ∀ x, x ∉ tsupport φ → h x = 0 := by
    intro x hx
    rw [hhdef]
    show φ x * w x = 0
    rw [hval0 φ x hx, zero_mul]
  have hhC1 : ContDiff ℝ 1 h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxU : x ∈ U
    · rw [hhdef]
      exact hφ1.contDiffAt.mul (hw.contDiffAt (hU.mem_nhds hxU))
    · have hxK : x ∉ tsupport φ := fun hc => hxU (hts hc)
      have hev : h =ᶠ[nhds x] fun _ : Plane => (0 : ℝ) := by
        filter_upwards [hKcl.isOpen_compl.mem_nhds hxK] with y hy using hh0 y hy
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  have hhsupp : HasCompactSupport h := HasCompactSupport.intro hKc hh0
  -- Step 2:  the integral of `D h` over the plane vanishes.
  have hzero : ∫ x : Plane, gradient h x = 0 := TestFunctionGradientIntegral h hhC1 hhsupp
  -- Step 3:  the product rule.  It holds at EVERY point, not only on `U`:  off `tsupport φ`
  -- both sides vanish, and `tsupport φ ⊆ U`.
  have hgrad : ∀ x, gradient h x = w x • gradient φ x + φ x • gradient w x := by
    intro x
    by_cases hxU : x ∈ U
    · have hwd : HasFDerivAt w (fderiv ℝ w x) x :=
        (((hw.differentiableOn one_ne_zero) x hxU).differentiableAt
          (hU.mem_nhds hxU)).hasFDerivAt
      have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
        (hφ1.differentiable one_ne_zero x).hasFDerivAt
      have hfd : fderiv ℝ h x = φ x • fderiv ℝ w x + w x • fderiv ℝ φ x := by
        rw [hhdef]
        exact (hφd.mul hwd).fderiv
      rw [hgr h x, hfd, map_add, map_smul, map_smul, ← hgr w x, ← hgr φ x]
      abel
    · have hxK : x ∉ tsupport φ := fun hc => hxU (hts hc)
      have hev : h =ᶠ[nhds x] fun _ : Plane => (0 : ℝ) := by
        filter_upwards [hKcl.isOpen_compl.mem_nhds hxK] with y hy using hh0 y hy
      rw [hev.gradient_eq, gradient_fun_const, hval0 φ x hxK, hgrad0 φ x hxK]
      simp
  -- Step 4:  both summands are integrable, each being continuous on the compact `tsupport φ`
  -- and vanishing off it.
  have hintR : ∀ (F : Plane → Plane), ContinuousOn F (tsupport φ) →
      (∀ y, y ∉ tsupport φ → F y = 0) → MeasureTheory.Integrable F := by
    intro F hFc hF0
    have hsupp' : Function.support F ⊆ tsupport φ := by
      intro y hy
      by_contra hc
      exact hy (hF0 y hc)
    rw [← Set.indicator_eq_self.mpr hsupp',
      MeasureTheory.integrable_indicator_iff hKc.measurableSet]
    exact ContinuousOn.integrableOn_compact hKc hFc
  have hint1 : MeasureTheory.Integrable (fun x => w x • gradient φ x) := by
    refine hintR _ ((hwc.mono hts).smul hdφc.continuousOn) ?_
    intro y hy
    rw [hgrad0 φ y hy, smul_zero]
  have hint2 : MeasureTheory.Integrable (fun x => φ x • gradient w x) := by
    refine hintR _ (hφ1.continuous.continuousOn.smul (hGc.mono hts)) ?_
    intro y hy
    rw [hval0 φ y hy, zero_smul]
  -- Step 5:  localization.  Each summand vanishes off `U`, so its integral over `U` is its
  -- integral over the plane.
  have hloc1 : ∫ x in U, w x • gradient φ x = ∫ x : Plane, w x • gradient φ x := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [hgrad0 φ x (fun hc => hx (hts hc)), smul_zero]
  have hloc2 : ∫ x in U, φ x • gradient w x = ∫ x : Plane, φ x • gradient w x := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [hval0 φ x (fun hc => hx (hts hc)), zero_smul]
  -- Conclusion.
  have hrw : (fun x : Plane => gradient h x)
      = fun x : Plane => w x • gradient φ x + φ x • gradient w x := funext hgrad
  rw [hrw, MeasureTheory.integral_add hint1 hint2] at hzero
  rw [hloc1, hloc2, eq_neg_iff_add_eq_zero]
  exact hzero
