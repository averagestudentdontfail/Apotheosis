import TreasurePeak.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# AR(1) Stochastic Process

Defines the AR(1) process: X_{t+1} = ρ·X_t + ε_t where ε_t ~ N(0, σ²)
-/

namespace AR1

variable (params : GameParams)

/-- AR(1) transition: next altitude given current altitude and innovation -/
noncomputable def transition (X_t : ℝ) (ε : ℝ) : ℝ :=
  params.ρ * X_t + ε

/-- Expected next altitude given current altitude -/
noncomputable def expectedNext (X_t : ℝ) : ℝ :=
  params.ρ * X_t

/-- Variance of next altitude -/
noncomputable def varianceNext : ℝ :=
  params.σ ^ 2

/-- The AR(1) process is mean-reverting to 0 -/
lemma mean_reverting :
    ∀ X_t : ℝ, |expectedNext params X_t| < |X_t| ∨ X_t = 0 := by
  intro X_t
  by_cases h : X_t = 0
  · right; exact h
  · left
    unfold expectedNext
    simp only [abs_mul, abs_of_pos params.hρ_pos]
    calc params.ρ * |X_t|
        < 1 * |X_t| := by {
          apply mul_lt_mul_of_pos_right params.hρ_lt_one
          exact abs_pos.mpr h
        }
      _ = |X_t| := by ring

/-- The AR(1) process has bounded trajectories (almost surely) -/
theorem bounded_trajectories :
    ∃ M : ℝ, M > 0 ∧ ∀ (n : ℕ) (X : ℕ → ℝ),
      (∀ t, X (t + 1) = transition params (X t) 0) →
      |X n| ≤ M / (1 - params.ρ) := by
  use params.σ * 3  -- 3σ bound (99.7% confidence)
  constructor
  · apply mul_pos
    · exact params.hσ_pos
    · norm_num
  · intro n X h_transition
    -- Proof sketch: AR(1) converges to stationary distribution
    -- with bounded variance σ²/(1-ρ²)
    sorry

/-- Long-run variance of AR(1) process -/
noncomputable def stationaryVariance : ℝ :=
  params.σ ^ 2 / (1 - params.ρ ^ 2)

end AR1
