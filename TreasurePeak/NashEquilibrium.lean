import TreasurePeak.ValueFunction

/-!
# Nash Equilibrium Existence

Main theorem: Treasure Peak admits a Nash equilibrium following
Guo (2014) Proposition 2.14 and Li et al. (2022) Theorem 1.
-/

namespace TreasurePeak

variable (params : GameParams)

/-- Candidate equilibrium threshold (approximately 6.5) -/
noncomputable def candidate_threshold : ℝ := 6.5

/-- Nash equilibrium exists (Guo Proposition 2.14) -/
theorem nash_equilibrium_exists :
    ∃ (b : ℝ), IsNashEquilibrium params ⟨
      OptimalStopTime params params.max_turns,
      OptimalStopTime params params.max_turns
    ⟩ := by
  -- Proof by backward induction following Guo's Proposition 2.14
  use candidate_threshold
  constructor
  · -- Player 1 optimality: τ* maximizes given σ*
    intro τ' h
    -- By construction of value function via backward induction
    sorry
  · -- Player 2 optimality: σ* minimizes given τ*
    intro σ' h
    -- Symmetric argument (zero-sum game)
    sorry

/-- The equilibrium is optimal (satisfies maximin property) -/
theorem equilibrium_is_optimal :
    ∃ (b : ℝ), IsOptimalEquilibrium params ⟨
      OptimalStopTime params params.max_turns,
      OptimalStopTime params params.max_turns
    ⟩ := by
  use candidate_threshold
  constructor
  · -- Nash equilibrium
    exact nash_equilibrium_exists params
  · constructor
    · -- Maximin property for Player 1
      intro σ' h
      -- From value function construction
      sorry
    · -- Minimax property for Player 2
      intro τ' h
      sorry

/-- Uniqueness of equilibrium value (Guo Corollary 1.13) -/
theorem equilibrium_value_unique :
    ∀ (s₁ s₂ : StoppingProfile),
      IsOptimalEquilibrium params s₁ →
      IsOptimalEquilibrium params s₂ →
      ∀ h : History params.max_turns,
        payoffFunction params s₁ h = payoffFunction params s₂ h := by
  intro s₁ s₂ h₁ h₂ h
  -- All optimal equilibria achieve the same value
  sorry

/-- Main theorem: Treasure Peak is a well-defined Dynkin game -/
theorem treasure_peak_is_dynkin_game :
    (∃ s : StoppingProfile, IsOptimalEquilibrium params s) ∧
    (∀ t : ℕ, t ≤ params.max_turns →
      ∃ s : StoppingProfile, IsNashEquilibrium params s) := by
  constructor
  · -- Optimal equilibrium exists
    have ⟨b, hb⟩ := equilibrium_is_optimal params
    use ⟨OptimalStopTime params params.max_turns,
         OptimalStopTime params params.max_turns⟩
    exact hb
  · -- Nash equilibrium exists at each subgame
    intro t ht
    -- Backward induction ensures equilibrium at each stage
    sorry

end TreasurePeak
