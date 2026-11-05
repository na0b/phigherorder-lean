import PHigherOrder.Plane

/-- `IsLinearDivSol Ω A w G` says that `w` is a continuous weak solution of the
linear divergence-form equation `div (A(x) Dw) = 0` on `Ω` with weak gradient `G`:
`w` is continuous on `Ω`, `G` is measurable with `|G|^2` locally integrable in `Ω`
(that is, `G ∈ L^2_loc(Ω)`), `G` is the distributional gradient of `w` on `Ω`, and the
equation holds in the weak sense against every test function supported in `Ω`. -/
structure IsLinearDivSol (Ω : Set Plane) (A : Plane → (Plane →L[ℝ] Plane))
    (w : Plane → ℝ) (G : Plane → Plane) : Prop where
  contW : ContinuousOn w Ω
  measG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Ω)
  locSqIntG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖G x‖ ^ 2) K
  weakGrad : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, w x • gradient φ x = - ∫ x in Ω, φ x • G x
  eqn : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, inner ℝ (A x (G x)) (gradient φ x) = (0 : ℝ)
