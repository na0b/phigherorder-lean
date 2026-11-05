import PHigherOrder.TaylorPoly

/-- Behaviour of the Taylor data under the paper's blow-up rescaling
`v_L(x) = v(R x) / R^σ` with `0 < R` (paper eq:coefficients and the normalization preceding
eq:approximation).

Two conclusions.

1. The jet identity, in diagonal form: for every `j ≤ k` and every direction `w`,
   `D^j v(0)[w,…,w] = R^(σ - j) · D^j v_L(0)[w,…,w]`.
   Taking absolute values recovers the paper's eq:coefficients verbatim.  For `j ≤ k` and
   `k < σ` the exponent `σ - j` is positive, which is what makes this a GAIN as `R → 0` and
   is the whole point of the rescaling in the paper's iteration; the node does not need that
   inequality and so does not assume it.

2. The polynomial identity `TaylorPoly k v 0 z = R^σ · TaylorPoly k v_L 0 (R⁻¹ • z)`, i.e. the
   degree-`k` Taylor polynomials of `v` and of `v_L` at the origin correspond under the same
   rescaling as the functions themselves.

The regularity hypothesis is LOCAL — `v` is only assumed `C^k` on some ball `ball 0 ρ` around
the origin — because that is all the consumers have: in section 3 of the paper `v` is
`p`-harmonic on `ball 0 1` and `C^k` only on a solution-dependent neighbourhood of a
non-critical point.  Mathlib's dilation rule for `iteratedFDeriv` requires global
`ContDiff`, so the identity is obtained instead from the within-a-set composition rule for a
continuous linear map, applied on `ball 0 ρ` and its preimage, both of which are open, and
transported to the ambient `iteratedFDeriv` there.

`v_L` is supplied as a function together with the defining equation `hvL` rather than written
out, so that a consumer may plug in whatever rescaled solution it has already constructed.

Conclusion 1 is DIAGONAL, and loses nothing: classically, for `j ≤ k` both
`iteratedFDeriv ℝ j v 0` and `iteratedFDeriv ℝ j vL 0` are SYMMETRIC, and two symmetric
`j`-linear forms with equal diagonal evaluations are equal by polarization, so conclusion 1 says
the same thing as the identity of full multilinear forms.  That is classical background about the
object: it is NOT a background item of this development and it is NOT a step available to any
proof in the tablet.  Mathlib at the pinned revision supplies symmetry of the iterated derivative
of a finitely smooth function only at order two, general order requiring analyticity, which is
why every statement here carries higher-order derivatives diagonally. -/
theorem TaylorPolyRescale (k : ℕ) (σ : ℝ) (v : Plane → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : ContDiffOn ℝ (k : ℕ∞) v (Metric.ball 0 ρ))
    (R : ℝ) (hR0 : 0 < R)
    (vL : Plane → ℝ) (hvL : ∀ x : Plane, vL x = v (R • x) / R ^ σ) :
    (∀ j : ℕ, j ≤ k → ∀ w : Plane,
        iteratedFDeriv ℝ j v 0 (fun _ => w)
          = R ^ (σ - (j : ℝ)) * iteratedFDeriv ℝ j vL 0 (fun _ => w))
      ∧ (∀ z : Plane, TaylorPoly k v 0 z = R ^ σ * TaylorPoly k vL 0 (R⁻¹ • z)) := by
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hRs : R ^ σ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR0 σ)
  -- the dilation, as a continuous linear map
  set L : Plane →L[ℝ] Plane := R • ContinuousLinearMap.id ℝ Plane with hL
  have hLapp : ∀ x : Plane, L x = R • x := fun x => rfl
  have hsopen : IsOpen (Metric.ball (0 : Plane) ρ) := Metric.isOpen_ball
  have hpreopen : IsOpen (L ⁻¹' Metric.ball (0 : Plane) ρ) := hsopen.preimage L.continuous
  have h0s : (0 : Plane) ∈ Metric.ball (0 : Plane) ρ := Metric.mem_ball_self hρ
  have hL0 : L 0 = (0 : Plane) := by rw [hLapp]; simp
  have h0pre : (0 : Plane) ∈ L ⁻¹' Metric.ball (0 : Plane) ρ := by
    simpa [Set.mem_preimage, hL0] using h0s
  have hcompCD : ContDiffOn ℝ (k : ℕ∞) (v ∘ L) (L ⁻¹' Metric.ball (0 : Plane) ρ) :=
    hv.comp L.contDiff.contDiffOn (Set.Subset.refl _)
  have hcompAt : ∀ j : ℕ, j ≤ k → ContDiffAt ℝ j (v ∘ L) 0 := fun j hj =>
    (hcompCD.contDiffAt (hpreopen.mem_nhds h0pre)).of_le (by exact_mod_cast hj)
  -- the derivative of `v ∘ L` at the origin, as a multilinear form
  have hstep : ∀ j : ℕ, j ≤ k → iteratedFDeriv ℝ j (v ∘ L) 0
      = (iteratedFDeriv ℝ j v 0).compContinuousLinearMap (fun _ => L) := by
    intro j hj
    have h := L.iteratedFDerivWithin_comp_right hv hsopen.uniqueDiffOn hpreopen.uniqueDiffOn
      (x := (0 : Plane)) (by simpa [hL0] using h0s) (i := j) (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen (f := v ∘ L) j hpreopen h0pre] at h
    rw [h, hL0, iteratedFDerivWithin_of_isOpen (f := v) j hsopen h0s]
  -- on the diagonal the linear map contributes `R ^ j`
  have hdiag : ∀ (j : ℕ) (w : Plane),
      (iteratedFDeriv ℝ j v 0).compContinuousLinearMap (fun _ => L) (fun _ => w)
        = R ^ (j : ℕ) * iteratedFDeriv ℝ j v 0 (fun _ => w) := by
    intro j w
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hrw : (fun _ : Fin j => L w) = fun _ : Fin j => R • w := by funext i; rw [hLapp]
    rw [hrw, (iteratedFDeriv ℝ j v 0).map_smul_univ (fun _ => R) (fun _ => w)]
    simp
  -- the jet identity, in the form that is convenient for both conclusions
  have hkey : ∀ j : ℕ, j ≤ k → ∀ w : Plane,
      iteratedFDeriv ℝ j vL 0 (fun _ => w)
        = (R ^ σ)⁻¹ * (R ^ (j : ℕ) * iteratedFDeriv ℝ j v 0 (fun _ => w)) := by
    intro j hj w
    have hvLeq : vL = fun x => (R ^ σ)⁻¹ • (v ∘ L) x := by
      funext x
      rw [hvL x]
      simp [Function.comp, hLapp, div_eq_inv_mul]
    rw [hvLeq, iteratedFDeriv_const_smul_apply' (hcompAt j hj), smul_apply, smul_eq_mul,
      hstep j hj, hdiag j w]
  have hmul : ∀ j : ℕ, R ^ (σ - (j : ℝ)) * R ^ (j : ℕ) = R ^ σ := by
    intro j
    rw [← Real.rpow_natCast R j, ← Real.rpow_add hR0]
    congr 1
    ring
  refine ⟨fun j hj w => ?_, fun z => ?_⟩
  · have h1 : R ^ (σ - (j : ℝ))
          * ((R ^ σ)⁻¹ * (R ^ (j : ℕ) * iteratedFDeriv ℝ j v 0 (fun _ => w)))
        = (R ^ (σ - (j : ℝ)) * R ^ (j : ℕ))
          * ((R ^ σ)⁻¹ * iteratedFDeriv ℝ j v 0 (fun _ => w)) := by
      ring
    rw [hkey j hj w, h1, hmul j, mul_inv_cancel_left₀ hRs]
  · simp only [TaylorPoly, sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := by have := Finset.mem_range.1 hj; omega
    have hhom : iteratedFDeriv ℝ j vL 0 (fun _ => R⁻¹ • z)
        = (R⁻¹) ^ (j : ℕ) * iteratedFDeriv ℝ j vL 0 (fun _ => z) := by
      rw [(iteratedFDeriv ℝ j vL 0).map_smul_univ (fun _ => R⁻¹) (fun _ => z)]
      simp
    rw [hhom, hkey j hjk z]
    field_simp
    rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hRne, one_pow, mul_one]
