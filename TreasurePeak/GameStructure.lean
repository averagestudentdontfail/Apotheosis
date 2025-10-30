import TreasurePeak.Basic
import TreasurePeak.AR1Process

/-!
# Game Structure

Defines Treasure Peak as a two-player competitive stopping game
following Guo (2014) Chapter 2.
-/

namespace TreasurePeak

variable (params : GameParams)

/-- Game history up to time t -/
structure History (t : ℕ) where
  altitudes : Fin t → ℝ
  oxygen_levels : Fin t → ℝ

/-- Stopping time: when a player decides to stop -/
abbrev StoppingTime := ℕ

/-- Simultaneous stopping times for both players -/
structure StoppingProfile where
  τ : StoppingTime  -- Player 1's stopping time
  σ : StoppingTime  -- Player 2's stopping time

/-- Get altitude at stopping time, with bounds checking -/
noncomputable def getAltitudeAt (h : History params.max_turns) (t : ℕ) : ℝ :=
  if ht : t < params.max_turns then
    h.altitudes ⟨t, ht⟩
  else if params.max_turns > 0 then
    h.altitudes ⟨params.max_turns - 1, by omega⟩
  else
    0  -- Fallback for max_turns = 0

/-- Payoff function following Guo's formulation (2.17) -/
noncomputable def payoffFunction (s : StoppingProfile) (h : History params.max_turns) : ℝ :=
  let final_altitude_1 := getAltitudeAt params h s.τ
  let final_altitude_2 := getAltitudeAt params h s.σ
  if s.τ < s.σ then
    final_altitude_1  -- Player 1 stopped first, gets that altitude
  else if s.σ < s.τ then
    0  -- Player 2 stopped first, Player 1 gets 0 (zero-sum)
  else
    final_altitude_1 / 2  -- Simultaneous stop, split value

/-- Nash equilibrium definition (Guo Definition 1.7) -/
def IsNashEquilibrium (s : StoppingProfile) : Prop :=
  -- Player 1 maximizes given Player 2's strategy
  (∀ τ' : StoppingTime, ∀ h : History params.max_turns,
    payoffFunction params ⟨τ', s.σ⟩ h ≤ payoffFunction params s h) ∧
  -- Player 2 minimizes Player 1's payoff (zero-sum)
  (∀ σ' : StoppingTime, ∀ h : History params.max_turns,
    payoffFunction params ⟨s.τ, σ'⟩ h ≥ payoffFunction params s h)

/-- Optimal equilibrium (Guo Definition 1.9): Nash + maximin property -/
def IsOptimalEquilibrium (s : StoppingProfile) : Prop :=
  IsNashEquilibrium params s ∧
  -- Player 1 can guarantee payoff without knowing Player 2's action
  (∀ σ' : StoppingTime, ∀ h : History params.max_turns,
    payoffFunction params ⟨s.τ, σ'⟩ h ≥
    payoffFunction params ⟨s.τ, s.σ⟩ h) ∧
  -- Player 2 can guarantee minimizing regardless of Player 1
  (∀ τ' : StoppingTime, ∀ h : History params.max_turns,
    payoffFunction params ⟨τ', s.σ⟩ h ≤
    payoffFunction params ⟨s.τ, s.σ⟩ h)

/-- Weakly Unilaterally Competitive (WUC) property (Guo Section 1.2.3) -/
def IsWUC : Prop :=
  ∀ (s s' : StoppingProfile) (h : History params.max_turns),
    (payoffFunction params s h ≤ payoffFunction params s' h) →
    -- If Player 1 is better off, Player 2 is worse off (zero-sum)
    (payoffFunction params s h = payoffFunction params s' h)

/-- Treasure Peak is zero-sum -/
theorem treasure_peak_zero_sum :
    ∀ (s : StoppingProfile) (h : History params.max_turns),
      ∃ v : ℝ, payoffFunction params s h + payoffFunction params ⟨s.σ, s.τ⟩ h = v := by
  intro s h
  use 0  -- Zero-sum: payoffs sum to constant
  sorry

/-- Treasure Peak is WUC (follows from zero-sum) -/
theorem treasure_peak_is_wuc : IsWUC params := by
  intro s s' h hineq
  -- Zero-sum games are WUC
  sorry

end TreasurePeak
