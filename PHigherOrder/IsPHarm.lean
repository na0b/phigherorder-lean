import PHigherOrder.PFlux

/-- `IsPHarm p Ω u g` says that `u` is a continuous `p`-harmonic function on the
open set `Ω` with weak gradient `g`:  `Ω` is open, `u` is continuous on `Ω`, `g` is
measurable with `|g|^p` locally integrable in `Ω` (that is, `g ∈ L^p_loc(Ω)`), `g`
is the distributional gradient of `u` on `Ω`, and `u` solves the `p`-Laplace
equation `-div (A_p g) = 0` weakly on `Ω`, where `A_p` is `PFlux p`. -/
structure IsPHarm (p : ℝ) (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane) : Prop where
  openOmega : IsOpen Ω
  contU : ContinuousOn u Ω
  measG : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Ω)
  locIntG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖g x‖ ^ p) K
  weakGrad : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, u x • gradient φ x = - ∫ x in Ω, φ x • g x
  eqn : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, inner ℝ (PFlux p (g x)) (gradient φ x) = (0 : ℝ)
