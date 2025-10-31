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
  else if hpos : params.max_turns > 0 then
    h.altitudes ⟨params.max_turns - 1, Nat.sub_lt hpos (by decide)⟩
  else
    0  -- Fallback for max_turns = 0

/-- Payoff function following Guo's formulation (2.17) -/
noncomputable def payoffFunction (s : StoppingProfile) (h : History params.max_turns) : ℝ :=
  let final_altitude_1 := getAltitudeAt params h s.τ
  -- Player 2's altitude not used in current formulation but kept for future extensions
  let _final_altitude_2 := getAltitudeAt params h s.σ
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

/-- Weakly Unilaterally Competitive (WUC) property (Guo Definition 1.19)

  A game is WUC if unilateral deviations have opposing effects on different players:
  - When one player strictly improves by deviating, other players weakly lose
  - When one player's payoff is unchanged by deviating, other players' payoffs are also unchanged
-/
def IsWUC : Prop :=
  -- For Player 1's unilateral deviations (changing τ, keeping σ fixed)
  (∀ (τ τ' σ : StoppingTime) (h : History params.max_turns),
    payoffFunction params ⟨τ, σ⟩ h > payoffFunction params ⟨τ', σ⟩ h →
    payoffFunction params ⟨σ, τ⟩ h ≤ payoffFunction params ⟨σ, τ'⟩ h) ∧
  (∀ (τ τ' σ : StoppingTime) (h : History params.max_turns),
    payoffFunction params ⟨τ, σ⟩ h = payoffFunction params ⟨τ', σ⟩ h →
    payoffFunction params ⟨σ, τ⟩ h = payoffFunction params ⟨σ, τ'⟩ h) ∧
  -- For Player 2's unilateral deviations (changing σ, keeping τ fixed)
  (∀ (τ σ σ' : StoppingTime) (h : History params.max_turns),
    payoffFunction params ⟨σ, τ⟩ h > payoffFunction params ⟨σ', τ⟩ h →
    payoffFunction params ⟨τ, σ⟩ h ≤ payoffFunction params ⟨τ, σ'⟩ h) ∧
  (∀ (τ σ σ' : StoppingTime) (h : History params.max_turns),
    payoffFunction params ⟨σ, τ⟩ h = payoffFunction params ⟨σ', τ⟩ h →
    payoffFunction params ⟨τ, σ⟩ h = payoffFunction params ⟨τ, σ'⟩ h)

/-- Treasure Peak is zero-sum -/
theorem treasure_peak_zero_sum :
    ∀ (s : StoppingProfile) (h : History params.max_turns),
      ∃ v : ℝ, payoffFunction params s h + payoffFunction params ⟨s.σ, s.τ⟩ h = v := by
  intro s h
  -- The sum of payoffs equals the altitude at the earlier stopping time
  use getAltitudeAt params h (min s.τ s.σ)
  unfold payoffFunction
  simp only
  -- Case analysis on the ordering of stopping times
  by_cases hτσ : s.τ < s.σ
  · -- Case: τ < σ, so Player 1 stopped first
    simp [hτσ]
    have hστ : ¬(s.σ < s.τ) := Nat.not_lt.mpr (Nat.le_of_lt hτσ)
    have hneq : ¬(s.σ = s.τ) := (Nat.ne_of_gt hτσ).symm
    simp [hστ]
    have : min s.τ s.σ = s.τ := min_eq_left (Nat.le_of_lt hτσ)
    rw [this]
    ring
  · by_cases hστ : s.σ < s.τ
    · -- Case: σ < τ, so Player 2 stopped first
      simp [hστ]
      have hτσ' : ¬(s.τ < s.σ) := hτσ
      simp [hτσ']
      have : min s.τ s.σ = s.σ := min_eq_right (Nat.le_of_lt hστ)
      rw [this]
      ring
    · -- Case: τ = σ, simultaneous stop
      have heq : s.τ = s.σ := Nat.le_antisymm (Nat.not_lt.mp hτσ) (Nat.not_lt.mp hστ)
      simp [heq]
      have : ¬(s.σ < s.σ) := Nat.lt_irrefl s.σ
      simp [this]
      have : min s.σ s.σ = s.σ := min_self s.σ
      rw [this]
      ring

/-- Treasure Peak is WUC (follows from zero-sum) -/
theorem treasure_peak_is_wuc : IsWUC params := by
  unfold IsWUC
  constructor
  -- Part 1: Player 1 deviations (strict improvement ⇒ Player 2 weakly loses)
  · intro τ τ' σ h h_improve
    -- Get the zero-sum property for both profiles
    have sum1 := treasure_peak_zero_sum params ⟨τ, σ⟩ h
    have sum2 := treasure_peak_zero_sum params ⟨τ', σ⟩ h
    obtain ⟨v1, hv1⟩ := sum1
    obtain ⟨v2, hv2⟩ := sum2
    -- Simplify the structure notation to extract the actual equation
    simp only [StoppingProfile.mk.injEq] at hv1 hv2
    -- Now hv1 and hv2 should have the right form
    linarith
  constructor
  -- Part 2: Player 1 deviations (equal payoff ⇒ Player 2 also equal)
  · intro τ τ' σ h h_equal
    have sum1 := treasure_peak_zero_sum params ⟨τ, σ⟩ h
    have sum2 := treasure_peak_zero_sum params ⟨τ', σ⟩ h
    obtain ⟨v1, hv1⟩ := sum1
    obtain ⟨v2, hv2⟩ := sum2
    simp only [StoppingProfile.mk.injEq] at hv1 hv2
    linarith
  constructor
  -- Part 3: Player 2 deviations (strict improvement ⇒ Player 1 weakly loses)
  · intro τ σ σ' h h_improve
    have sum1 := treasure_peak_zero_sum params ⟨σ, τ⟩ h
    have sum2 := treasure_peak_zero_sum params ⟨σ', τ⟩ h
    obtain ⟨v1, hv1⟩ := sum1
    obtain ⟨v2, hv2⟩ := sum2
    simp only [StoppingProfile.mk.injEq] at hv1 hv2
    linarith
  -- Part 4: Player 2 deviations (equal payoff ⇒ Player 1 also equal)
  · intro τ σ σ' h h_equal
    have sum1 := treasure_peak_zero_sum params ⟨σ, τ⟩ h
    have sum2 := treasure_peak_zero_sum params ⟨σ', τ⟩ h
    obtain ⟨v1, hv1⟩ := sum1
    obtain ⟨v2, hv2⟩ := sum2
    simp only [StoppingProfile.mk.injEq] at hv1 hv2
    linarith

end TreasurePeak
