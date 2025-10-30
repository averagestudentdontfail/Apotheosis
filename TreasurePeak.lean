import TreasurePeak.Basic
import TreasurePeak.AR1Process
import TreasurePeak.GameStructure
import TreasurePeak.ValueFunction
import TreasurePeak.NashEquilibrium
import TreasurePeak.Verification

/-!
# Treasure Peak: A Dynkin Stopping Game

This project formalizes Treasure Peak as a two-player competitive stopping game,
proving it satisfies the properties of a Dynkin game following:
- Guo (2014): Competitive Multi-Player Stochastic Games
- Li et al. (2022): Closed-Form Solutions for Distributionally Robust Inventory Management

## Main Results

1. **Nash Equilibrium Exists** (`nash_equilibrium_exists`):
   Treasure Peak admits a Nash equilibrium at threshold b* ≈ 6.5

2. **Optimal Equilibrium** (`equilibrium_is_optimal`):
   The equilibrium satisfies the maximin property (players can guarantee payoffs)

3. **Dynkin Game Properties** (`treasure_peak_is_dynkin_game`):
   Treasure Peak satisfies all requirements of a Dynkin stopping game

## Project Structure

- `Basic.lean`: Core definitions (actions, strategies, payoffs)
- `AR1Process.lean`: Stochastic altitude process X_{t+1} = ρX_t + ε_t
- `GameStructure.lean`: Game-theoretic framework
- `ValueFunction.lean`: Backward induction via recursive value function
- `NashEquilibrium.lean`: Main existence theorems
- `Verification.lean`: Numerical verification of b* ≈ 6.5
-/

#check TreasurePeak.nash_equilibrium_exists
#check TreasurePeak.equilibrium_is_optimal
#check TreasurePeak.treasure_peak_is_dynkin_game
