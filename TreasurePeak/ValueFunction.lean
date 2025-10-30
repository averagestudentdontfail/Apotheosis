import TreasurePeak.GameStructure
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Value Function via Backward Induction

Following Guo (2014) Definition 2.9 and Proposition 2.14.
Constructs the value function recursively from terminal time.
-/

namespace TreasurePeak

variable (params : GameParams)

/-- Value function at time t, altitude θ, following Guo's Definition 2.9 -/
noncomputable def ValueFunction : ℕ → ℝ → ℝ
  | 0, θ => θ  -- Terminal: must grab current value
  | t + 1, θ =>
      -- Guo's equation (2.20): V_t = max(L_t, min(U_t, E[V_{t+1}]))
      -- Here: L_t = stopping value, U_t = continuation value
      max θ (AR1.expectedNext params θ * ValueFunction t (AR1.expectedNext params θ))

/-- Lower barrier L_t: value if stop immediately (Guo Section 2.1.2) -/
noncomputable def LowerBarrier (t : ℕ) (θ : ℝ) : ℝ := θ

/-- Upper barrier U_t: value if opponent stops (Guo Section 2.1.2) -/
noncomputable def UpperBarrier (t : ℕ) (θ : ℝ) : ℝ :=
  AR1.expectedNext params θ

/-- Optimal stopping time following Guo's Definition 2.9, equations (2.21-2.22) -/
noncomputable def OptimalStopTime (t : ℕ) : ℝ :=
  -- First crossing: min {u ≥ t | V_u = L_u}
  -- This is the threshold b*
  Classical.epsilon (λ b : ℝ => ∀ θ ≥ b, ValueFunction params t θ = θ)

/-- Value function properties (Guo Lemma 2.10) -/
theorem value_function_bounded (t : ℕ) (θ : ℝ) :
    LowerBarrier t θ ≤ ValueFunction params t θ ∧
    ValueFunction params t θ ≤ UpperBarrier params t θ := by
  cases t with
  | zero =>
      -- Base case: V_0(θ) = θ
      constructor
      · unfold ValueFunction LowerBarrier; linarith
      · unfold ValueFunction UpperBarrier AR1.expectedNext
        -- At terminal time, must stop
        sorry
  | succ t' =>
      -- Inductive case
      constructor
      · -- V_t ≥ L_t (can always stop)
        unfold ValueFunction LowerBarrier
        apply le_max_left
      · -- V_t ≤ U_t (opponent can stop)
        sorry

/-- Existence condition (Guo's Assumption 2.11): X_t ∧ Y_t ≤ V_t ≤ X_t ∨ Y_t -/
theorem existence_condition (t : ℕ) (θ : ℝ) :
    θ ≤ ValueFunction params t θ := by
  cases t with
  | zero =>
      unfold ValueFunction; linarith
  | succ t' =>
      unfold ValueFunction
      apply le_max_left

/-- Value function is monotone in altitude -/
theorem value_function_monotone (t : ℕ) :
    Monotone (ValueFunction params t) := by
  intro θ₁ θ₂ h
  cases t with
  | zero =>
      -- Base case: V_0 is identity
      unfold ValueFunction
      exact h
  | succ t' =>
      -- Inductive case
      unfold ValueFunction
      sorry

/-- Optimal threshold exists and is unique -/
theorem optimal_threshold_exists_unique (t : ℕ) :
    ∃! b : ℝ, ∀ θ : ℝ, (θ ≥ b → ValueFunction params t θ = θ) ∧
                       (θ < b → ValueFunction params t θ > θ) := by
  sorry

end TreasurePeak
