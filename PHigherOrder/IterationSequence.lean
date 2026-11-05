import PHigherOrder.Plane

/-- The radii of the paper's main iteration (paper lines 228-247), built as a TOTAL recursion
with a guarded step.

The paper's construction is PARTIAL: `R_0 = 1`, and `R_{l+1} = R_l rho_i` is defined only when
the continuation condition `|Dv_l(0)| <= delta` holds, the construction stopping otherwise.
Lean will not accept a sequence undefined past a stopping index.  The resolution is to make the
recursion total by STALLING: at a radius where `Good` or `Cont` fails the step returns the same
radius.  Stalling preserves `Good`, so `Good (R l)` holds for EVERY `l`, and the two-sided
bound on `R (l+1)` is asserted only under `Cont (R l)`, so it is vacuous exactly where the
chain stalls.  That is faithful to the paper, which itself says the bounds involving `R_{l+1}`
"apply whenever the next scale is constructed".

`Good` is the normalization package carried at each scale and `Cont` the continuation
condition; the consumer instantiates them as
`Good R = (∀ y, ‖y‖ < R → |v y| ≤ R ^ sigma)` and
`Cont R = (R ^ (1 - sigma) * ‖gradient v 0‖ ≤ delta)`, which is how `IterationStep` supplies
the hypothesis `hstep`. -/
theorem IterationSequence (Good Cont : ℝ → Prop) (θ : ℝ)
    (hGood1 : Good 1)
    (hstep : ∀ R : ℝ, Good R → Cont R → ∃ R' : ℝ, Good R' ∧ θ * R ≤ R' ∧ R' ≤ R / 4) :
    ∃ R : ℕ → ℝ, R 0 = 1 ∧ (∀ l : ℕ, Good (R l)) ∧
      ∀ l : ℕ, Cont (R l) → (θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) := by
  have hstep' : ∀ R : ℝ, ∃ R' : ℝ,
      (Good R → Cont R → (Good R' ∧ θ * R ≤ R' ∧ R' ≤ R / 4))
        ∧ (¬ (Good R ∧ Cont R) → R' = R) := by
    intro R
    by_cases hGC : Good R ∧ Cont R
    · obtain ⟨R', hR'⟩ := hstep R hGC.1 hGC.2
      exact ⟨R', fun _ _ => hR', fun h => absurd hGC h⟩
    · exact ⟨R, fun hG hC => absurd ⟨hG, hC⟩ hGC, fun _ => rfl⟩
  choose f hf1 hf2 using hstep'
  set seq : ℕ → ℝ := fun l => Nat.rec (1 : ℝ) (fun _ r => f r) l with hseq
  have hsucc : ∀ l : ℕ, seq (l + 1) = f (seq l) := fun l => rfl
  have hGoodAll : ∀ l, Good (seq l) := by
    intro l
    induction l with
    | zero => exact hGood1
    | succ n ih =>
      rw [hsucc]
      by_cases hC : Cont (seq n)
      · exact (hf1 _ ih hC).1
      · rw [hf2 _ (fun h => hC h.2)]; exact ih
  refine ⟨seq, rfl, hGoodAll, ?_⟩
  intro l hC
  rw [hsucc]
  exact ⟨(hf1 _ (hGoodAll l) hC).2.1, (hf1 _ (hGoodAll l) hC).2.2⟩
