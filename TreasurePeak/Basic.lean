import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Basic Definitions for Treasure Peak

This file contains the fundamental definitions for modeling Treasure Peak
as a Dynkin stopping game.
-/

/-- Game parameters for Treasure Peak -/
structure GameParams where
  ρ : ℝ                    -- Mean reversion coefficient
  σ : ℝ                    -- Volatility
  max_turns : ℕ            -- Maximum number of turns (15)
  initial_oxygen : ℝ       -- Starting oxygen (100%)
  hρ_pos : 0 < ρ
  hρ_lt_one : ρ < 1
  hσ_pos : 0 < σ

/-- Game state at any point in time -/
structure GameState where
  turn : ℕ                 -- Current turn number
  altitude : ℝ             -- Current altitude/value
  oxygen : ℝ               -- Remaining oxygen percentage

/-- Player action: Stop (grab) or Continue (climb) -/
inductive Action where
  | stop : Action
  | continue : Action
  deriving Repr, DecidableEq

/-- Strategy: maps game state to action -/
def Strategy := GameState → Action

/-- Threshold strategy: stop when altitude ≥ threshold -/
noncomputable def ThresholdStrategy (b : ℝ) : Strategy :=
  fun s => if s.altitude ≥ b then Action.stop else Action.continue

/-- Winner determination: highest altitude wins (zero-sum) -/
structure Outcome where
  player1_altitude : ℝ
  player2_altitude : ℝ

noncomputable def winner (o : Outcome) : Option ℕ :=
  if o.player1_altitude > o.player2_altitude then some 1
  else if o.player2_altitude > o.player1_altitude then some 2
  else none

/-- Payoff: 1 if win, 0 if lose (zero-sum game) -/
noncomputable def payoff (player : ℕ) (o : Outcome) : ℝ :=
  match winner o with
  | some n => if n = player then 1 else 0
  | none => 0  -- Draw pays 0

namespace TreasurePeak

/-- Oxygen consumption per turn -/
noncomputable def oxygenCost (altitude : ℝ) : ℝ :=
  0.03 + (altitude / 10) * 0.07

/-- Check if oxygen constraint is violated -/
def oxygenViolated (oxygen : ℝ) : Prop :=
  oxygen ≤ 0

/-- Check if turn limit reached -/
def turnLimitReached (params : GameParams) (turn : ℕ) : Prop :=
  turn ≥ params.max_turns

end TreasurePeak
