import PHigherOrder.Plane

/-- The classical gradient field is the Riesz transport of the Frechet derivative, and the
order-`n` jet of the gradient field is ISOMETRIC to the order-`(n+1)` jet of the scalar.

For an open `U` and a function `v` that is `C^∞` on `U`, four facts:

* (1) the FACTORIZATION `Dv = J⁻¹ ∘ D¹v`, where `J⁻¹` is the inverse Riesz map
  `(Plane →L[ℝ] ℝ) ≃ₗᵢ Plane`.  This is needed at all because the order-shift proposition
  differentiates `D¹v : Plane → (Plane →L[ℝ] ℝ)`, which takes values in the DUAL of the plane,
  whereas the classical gradient field `Dv : Plane → Plane` takes values in the plane itself,
  and this development keeps the two apart;
* (2) the gradient field inherits `C^∞` on `U` from `v`;
* (3) the ONE-POINT order shift `‖D^n (Dv) x‖ = ‖D^(n+1) v x‖`.  This one needs no domain and no
  regularity: it follows from (1) alone, since post-composition with the Riesz isometry and the
  order-shift isometry each preserve the norm of an iterated derivative, so it is stated for
  every `x : Plane`;
* (4) the TWO-POINT order shift, the same identity on a difference of jets at two points of `U`.
  A Holder seminorm is a two-point difference, so (3) does not give it: the two isometries have
  to be moved outside the difference, which needs them to be LINEAR as well as norm-preserving,
  and moving the Riesz map outside the iterated derivative at a point of `U` needs `ContDiffAt`
  there -- which is why this clause, unlike (3), is restricted to `U`.

Every clause is an EQUALITY: no constant is lost in the passage between a scalar function and its
gradient field.  This is the bridge the Schauder bootstrap of the paper's lem:noncritical crosses
in both directions -- it carries its inductive hypothesis on the scalar `v` but applies its
composition estimate and its divergence-form input to the gradient field `Dv`. -/
theorem GradientFieldOrderShift (U : Set Plane) (v : Plane → ℝ)
    (hUo : IsOpen U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    gradient v
        = (fun T : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm T) ∘ fderiv ℝ v
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (gradient v) U
      ∧ (∀ (n : ℕ) (x : Plane),
          ‖iteratedFDeriv ℝ n (gradient v) x‖ = ‖iteratedFDeriv ℝ (n + 1) v x‖)
      ∧ (∀ (n : ℕ), ∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ n (gradient v) x - iteratedFDeriv ℝ n (gradient v) y‖
            = ‖iteratedFDeriv ℝ (n + 1) v x - iteratedFDeriv ℝ (n + 1) v y‖) := by
  -- (1) THE RIESZ FACTORIZATION.  Pointwise, `D¹v z` is the Riesz dual of `gradient v z`.
  have hgfac : gradient v
      = (fun T : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm T) ∘ fderiv ℝ v := by
    funext z
    show gradient v z = (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ v z)
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨hgfac, ?_, ?_, ?_⟩
  -- (2) SMOOTHNESS.  The Riesz map is a continuous linear equivalence, hence `C^∞`, and `D¹v`
  -- is `C^∞` on the OPEN set `U` because `v` is.
  · rw [hgfac]
    exact (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp_contDiffOn
      (hv.fderiv_of_isOpen hUo (by norm_cast))
  -- (3) THE ONE-POINT ORDER SHIFT.  Two isometries, no domain hypothesis.
  · intro n x
    rw [hgfac, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]
  -- (4) THE TWO-POINT ORDER SHIFT.
  · intro n x hx y hy
    obtain ⟨Λ, hΛ⟩ : ∃ t : (Plane →L[ℝ] ℝ) →L[ℝ] Plane,
        t = (InnerProductSpace.toDual ℝ Plane).symm.toLinearIsometry.toContinuousLinearMap :=
      ⟨_, rfl⟩
    have hgfac' : gradient v = (fun T : Plane →L[ℝ] ℝ => Λ T) ∘ fderiv ℝ v := by
      rw [hΛ]; exact hgfac
    -- (i) move the Riesz map outside the iterated derivative, at both points
    have hstr : ∀ z ∈ U, iteratedFDeriv ℝ n (gradient v) z
        = Λ.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) z) := by
      intro z hz
      have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ v) z :=
        (hv.contDiffAt (hUo.mem_nhds hz)).fderiv_right (by norm_cast)
      rw [hgfac']
      exact Λ.iteratedFDeriv_comp_left hcd (by exact_mod_cast le_top)
    rw [hstr x hx, hstr y hy,
      show Λ.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) x)
          - Λ.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) y)
          = Λ.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n (fderiv ℝ v) x - iteratedFDeriv ℝ n (fderiv ℝ v) y)
        from by ext u; simp, hΛ,
      LinearIsometry.norm_compContinuousMultilinearMap]
    -- (ii) the order shift, on the difference
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
    show _ = ‖(continuousMultilinearCurryRightEquiv' ℝ n Plane ℝ).symm
          (iteratedFDeriv ℝ n (fun z => fderiv ℝ v z) x)
        - (continuousMultilinearCurryRightEquiv' ℝ n Plane ℝ).symm
          (iteratedFDeriv ℝ n (fun z => fderiv ℝ v z) y)‖
    rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
