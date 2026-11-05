import PHigherOrder.Plane

/-- The dichotomy of the paper's main iteration (paper lines 247-255), stated for a chain of
radii supplied as a HYPOTHESIS rather than rebuilt: `IterationSequence` constructs such a
chain and `IterationStep` supplies its guarded step, so this node consumes the chain and
extracts the two branches the main proof then treats separately.

Writing `sigma` for the paper's `k + beta` and `Cont R` for the continuation condition
`R ^ (1 - sigma) * ‖gradient v 0‖ ≤ delta`, which is the paper's `|Dv_l(0)| ≤ delta` expressed
through `v` and the radius, the three conclusions are the paper's three assertions:

1. the iteration continues indefinitely exactly when `Dv(0) = 0`.  One direction is immediate;
   the other is the paper's argument that an infinite iteration forces `R_l → 0` and hence
   `|Dv_l(0)| → ∞`, since `sigma > 1`, contradicting the continuation condition;
2. in the infinite branch, `R_l → 0` and `v` decays at the paper's rate,
   `|v y| ≤ theta^(-sigma) * r^sigma` for `‖y‖ < r` and every `0 < r ≤ 1` — the paper states it
   between consecutive constructed scales, and choosing the scale for a given `r` gives it for
   all `r` at once, which is the form eq:approximation needs;
3. in the finite branch there is a LEAST index `L` at which the continuation condition fails,
   which is the `L` the paper introduces before applying lem:noncritical to `v_L`.

The hypothesis `hsand` is guarded by the continuation condition, exactly as
`IterationSequence` delivers it, so nothing is assumed about `R (l+1)` where the chain
stalls. -/
theorem IterationDichotomy (σ δ θ : ℝ) (hσ : 1 < σ) (hδ : 0 < δ) (hθ0 : 0 < θ)
    (v : Plane → ℝ) (R : ℕ → ℝ) (hR0 : R 0 = 1) (hRpos : ∀ l : ℕ, 0 < R l)
    (hGood : ∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ σ)
    (hsand : ∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ →
        θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) :
    ((∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) ↔ gradient v 0 = 0)
      ∧ ((∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) →
          Filter.Tendsto R Filter.atTop (nhds 0)
            ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y : Plane, ‖y‖ < r → |v y| ≤ θ ^ (-σ) * r ^ σ)
      ∧ (gradient v 0 ≠ 0 →
          ∃ L : ℕ, ¬ (R L ^ (1 - σ) * ‖gradient v 0‖ ≤ δ)
            ∧ ∀ l < L, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  -- STEP 1:  under full continuation the radii decay geometrically, hence to `0`.
  have hgeo : (∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) →
      Filter.Tendsto R Filter.atTop (nhds 0) := by
    intro hcont
    have hquart : ∀ l : ℕ, R l ≤ (1 / 4 : ℝ) ^ l := by
      intro l
      induction l with
      | zero => rw [hR0]; norm_num
      | succ n ih =>
        have h := (hsand n (hcont n)).2
        calc R (n + 1) ≤ R n / 4 := h
          _ ≤ (1 / 4 : ℝ) ^ n / 4 := by linarith
          _ = (1 / 4 : ℝ) ^ (n + 1) := by ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ)) (h := fun l : ℕ => (1 / 4 : ℝ) ^ l)
      tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (fun l => le_of_lt (hRpos l)) hquart
  -- STEP 2:  conclusion (1).
  have hback : gradient v 0 = 0 → ∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ := by
    intro h0 l
    rw [h0, norm_zero, mul_zero]
    exact le_of_lt hδ
  have hfwd : (∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) → gradient v 0 = 0 := by
    intro hcont
    by_contra hne
    have hc : 0 < ‖gradient v 0‖ := norm_pos_iff.mpr hne
    have hinv : ∀ l : ℕ, R l ^ (1 - σ) = (R l ^ (σ - 1))⁻¹ := by
      intro l
      rw [show (1 - σ) = -(σ - 1) by ring, Real.rpow_neg (le_of_lt (hRpos l))]
    have hkey : ∀ l : ℕ, ‖gradient v 0‖ / δ ≤ R l ^ (σ - 1) := by
      intro l
      have hp : 0 < R l ^ (σ - 1) := Real.rpow_pos_of_pos (hRpos l) _
      have h := hcont l
      rw [hinv l, inv_mul_eq_div, div_le_iff₀ hp] at h
      rw [div_le_iff₀ hδ]
      linarith
    have htend : Filter.Tendsto (fun l => R l ^ (σ - 1)) Filter.atTop (nhds 0) := by
      have h := (hgeo hcont).rpow_const (Or.inr (le_of_lt hσ1))
      rwa [Real.zero_rpow (ne_of_gt hσ1)] at h
    obtain ⟨l, hl⟩ :=
      (Filter.Tendsto.eventually_lt_const (div_pos hc hδ) htend).exists
    exact absurd (hkey l) (not_le.mpr hl)
  refine ⟨⟨hfwd, hback⟩, ?_, ?_⟩
  · -- STEP 3:  conclusion (2).
    intro hcont
    refine ⟨hgeo hcont, ?_⟩
    intro r hr0 hr1 y hy
    -- bracket `r` between consecutive radii;  `R` is not assumed monotone
    have hev : ∀ᶠ l in Filter.atTop, R l < r :=
      Filter.Tendsto.eventually_lt_const hr0 (hgeo hcont)
    obtain ⟨Nn, hNn⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨ℓ, hℓdef⟩ : ∃ m : ℕ, m = Nat.findGreatest (fun l => r ≤ R l) Nn := ⟨_, rfl⟩
    have hP0 : r ≤ R 0 := by rw [hR0]; exact hr1
    have hℓP : r ≤ R ℓ := by
      rw [hℓdef]
      exact Nat.findGreatest_spec (P := fun l => r ≤ R l) (Nat.zero_le Nn) hP0
    have hnext : R (ℓ + 1) < r := by
      by_cases hle : ℓ + 1 ≤ Nn
      · have hgr := Nat.findGreatest_is_greatest (k := ℓ + 1) (P := fun l => r ≤ R l) (n := Nn)
          (by rw [← hℓdef]; omega) hle
        exact not_le.mp hgr
      · exact hNn (ℓ + 1) (by omega)
    have hgood : |v y| ≤ R ℓ ^ σ := hGood ℓ y (lt_of_lt_of_le hy hℓP)
    have hRlt : R ℓ < r * θ⁻¹ := by
      have h2 : θ * R ℓ < r := lt_of_le_of_lt (hsand ℓ (hcont ℓ)).1 hnext
      rw [← div_eq_mul_inv]
      exact (lt_div_iff₀' hθ0).mpr h2
    calc |v y| ≤ R ℓ ^ σ := hgood
      _ ≤ (r * θ⁻¹) ^ σ :=
          Real.rpow_le_rpow (le_of_lt (hRpos ℓ)) (le_of_lt hRlt) (le_of_lt hσ0)
      _ = r ^ σ * (θ⁻¹) ^ σ :=
          Real.mul_rpow (le_of_lt hr0) (le_of_lt (inv_pos.mpr hθ0))
      _ = r ^ σ * (θ ^ σ)⁻¹ := by rw [Real.inv_rpow (le_of_lt hθ0)]
      _ = θ ^ (-σ) * r ^ σ := by rw [← Real.rpow_neg (le_of_lt hθ0)]; ring
  · -- STEP 4:  conclusion (3), the LEAST failing index.
    intro hne
    have hex : ∃ l : ℕ, ¬ (R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) :=
      not_forall.mp (fun h => hne (hfwd h))
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro l hl
    exact not_not.mp (Nat.find_min hex hl)
