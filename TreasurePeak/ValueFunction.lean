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
noncomputable def LowerBarrier (_t : ℕ) (θ : ℝ) : ℝ := θ

/-- Upper barrier U_t: value if opponent stops (Guo Section 2.1.2) -/
noncomputable def UpperBarrier (_t : ℕ) (θ : ℝ) : ℝ :=
  AR1.expectedNext params θ

/-- Optimal threshold b* following Guo's Definition 2.9, equations (2.21-2.22) -/
noncomputable def OptimalThreshold (t : ℕ) : ℝ :=
  -- Threshold where stopping becomes optimal: {b | V_t(b) = b}
  Classical.epsilon (fun b : ℝ => ∀ θ ≥ b, ValueFunction params t θ = θ)

/-- Optimal stopping time: first time altitude crosses threshold -/
noncomputable def OptimalStopTime (t : ℕ) (h : History params.max_turns) : StoppingTime :=
  -- First crossing: min {u ≥ t | altitude_u ≥ b*}
  Classical.epsilon (fun u : ℕ => 
    u < params.max_turns ∧ 
    getAltitudeAt params h u ≥ OptimalThreshold params t)

/-- Value function properties (Guo Lemma 2.10) -/
theorem value_function_bounded (t : ℕ) (θ : ℝ) :
    LowerBarrier t θ ≤ ValueFunction params t θ ∧
    ValueFunction params t θ ≤ UpperBarrier params t θ := by
  cases t with
  | zero =>
      -- Base case: V_0(θ) = θ
      simp [ValueFunction, LowerBarrier, UpperBarrier, AR1.expectedNext]
      sorry
  | succ _t' =>
      -- Inductive case
      simp [ValueFunction, LowerBarrier, UpperBarrier]
      sorry

/-- Existence condition (Guo's Assumption 2.11): X_t ∧ Y_t ≤ V_t ≤ X_t ∨ Y_t -/
theorem existence_condition (t : ℕ) (θ : ℝ) :
    θ ≤ ValueFunction params t θ := by
  cases t with
  | zero =>
      simp [ValueFunction]
  | succ _t' =>
      simp [ValueFunction]

/-- Value function is monotone in altitude -/
theorem value_function_monotone (t : ℕ) :
    Monotone (ValueFunction params t) := by
  intro θ₁ θ₂ h
  cases t with
  | zero =>
      -- Base case: V_0 is identity
      simp [ValueFunction]
      exact h
  | succ _t' =>
      -- Inductive case
      simp [ValueFunction]
      sorry

/-- Optimal threshold exists and is unique -/
theorem optimal_threshold_exists_unique (t : ℕ) :
    ∃! b : ℝ, ∀ θ : ℝ, (θ ≥ b → ValueFunction params t θ = θ) ∧
                       (θ < b → ValueFunction params t θ > θ) := by
  sorry

end TreasurePeak
