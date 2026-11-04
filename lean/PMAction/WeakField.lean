import PMSubstrate.Impedance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The gravitational weak-field reconstruction from the capacity ledger

Paper II §7 proposes a capacity ledger `C(x) = ν − K(x)`, a refractive index
`n = ν/C` and a clock speed `c_loc = C/ν`, together with the weak-field relations
`g_00 ≈ −(1 − K/ν)` and `Φ ≈ −K/(2ν)`, and the identification
`g_00 ≈ −(1 + 2Φ)`. It notes these do not follow from the deficit alone and need a
derived propagation/response law. This module checks the *algebraic reconstruction*
and states exactly what the deficit does and does not supply.

**What is proved here.**
* `available`, `localIndex`, `clockSpeed` — the capacity ledger `ν−K`, `ν/(ν−K)`,
  `(ν−K)/ν`.
* `g00Linear`, `PhiLinear` — the paper's *proposed* linearized pair
  `−(1 − K/ν)`, `−K/(2ν)`, with `g00Linear = −(1 + 2Φ)` (`g00Linear_eq`).
* `g00`, `Phi` — the *exact clock-squared* pair `−c_loc²`, `(c_loc²−1)/2`, also
  satisfying the identification (`g00_eq`), with `Phi = −K/ν + K²/(2ν²)`
  (`Phi_eq`). It is strictly attractive for `0 < K < ν` (`Phi_neg`).
* `Phi_eq_linear` — the exact potential is **twice** the linearized proposal at
  leading order plus `K²/(2ν²)`. So the two candidate readouts are different; the
  response law must select one.
* `clockSpeed_at_capacity`, `g00_at_capacity` — at `K = ν` the clock stops and
  `g_00 = 0`. This is a *local* statement; a horizon is global and not proved here.

**What is not proved.** The propagation/response law that would select `c_loc` and
the weak-field ansatz, the spatial metric, the field equation, and the global
causal structure. The capacity deficit alone supplies neither.
-/

noncomputable section
namespace PMAction.WeakField
open PMSubstrate

/-- Paper I's derived channel capacity `ν = 16`. -/
def channelCapacity : ℝ := (PMSubstrate.baseline.sectorChannels : ℝ)

theorem channelCapacity_eq : channelCapacity = 16 := by
  norm_num [channelCapacity, PMSubstrate.baseline]

/-- Available capacity `C(x) = ν − K`. -/
def available (nu K : ℝ) : ℝ := nu - K

/-- Local refractive index `n = ν/(ν−K)`. -/
def localIndex (nu K : ℝ) : ℝ := nu / (nu - K)

/-- Local clock speed `c_loc = (ν−K)/ν` in units `c = 1`. -/
def clockSpeed (nu K : ℝ) : ℝ := (nu - K) / nu

/-- Paper §7 linearized time-time component `g_00 = −(1 − K/ν)`. -/
def g00Linear (nu K : ℝ) : ℝ := -(1 - K / nu)

/-- Paper §7 linearized Newtonian potential `Φ = −K/(2ν)`. -/
def PhiLinear (nu K : ℝ) : ℝ := -K / (2 * nu)

/-- **The identification holds for the proposed pair**: `g_00 = −(1 + 2Φ)`. -/
theorem g00Linear_eq (nu K : ℝ) :
    g00Linear nu K = -(1 + 2 * PhiLinear nu K) := by
  unfold g00Linear PhiLinear
  ring

/-- The proposed potential is attractive for a positive load. -/
theorem PhiLinear_neg (nu K : ℝ) (hnu : 0 < nu) (hK : 0 < K) :
    PhiLinear nu K < 0 := by
  unfold PhiLinear
  apply div_neg_of_neg_of_pos <;> nlinarith

/-- Exact clock-squared time-time component `g_00 = −c_loc²`. -/
def g00 (nu K : ℝ) : ℝ := -(clockSpeed nu K) ^ 2

/-- Exact Newtonian potential `Φ = (c_loc² − 1)/2`. -/
def Phi (nu K : ℝ) : ℝ := ((clockSpeed nu K) ^ 2 - 1) / 2

/-- **The identification holds for the exact pair too**: `g_00 = −(1 + 2Φ)`. -/
theorem g00_eq (nu K : ℝ) : g00 nu K = -(1 + 2 * Phi nu K) := by
  unfold g00 Phi
  ring

/-- Exact weak-load form of the potential: `Φ = −K/ν + K²/(2ν²)`. -/
theorem Phi_eq (nu K : ℝ) (hnu : nu ≠ 0) :
    Phi nu K = -K / nu + K ^ 2 / (2 * nu ^ 2) := by
  unfold Phi clockSpeed
  field_simp
  ring

/-- The exact potential is strictly attractive below capacity. -/
theorem Phi_neg (nu K : ℝ) (hnu : 0 < nu) (hK : 0 < K) (hKnu : K < nu) :
    Phi nu K < 0 := by
  rw [Phi_eq nu K hnu.ne']
  have h : -K / nu + K ^ 2 / (2 * nu ^ 2) = (K ^ 2 - 2 * K * nu) / (2 * nu ^ 2) := by
    field_simp
    ring
  rw [h]
  apply div_neg_of_neg_of_pos
  · nlinarith
  · positivity

/-- **The exact and linearized proposals differ.** The exact potential is
`2·Φ_linear + K²/(2ν²)`, i.e. twice the linearized proposal at leading order. -/
theorem Phi_eq_linear (nu K : ℝ) (hnu : nu ≠ 0) :
    Phi nu K = 2 * PhiLinear nu K + K ^ 2 / (2 * nu ^ 2) := by
  rw [Phi_eq nu K hnu]
  unfold PhiLinear
  ring

/-- Below capacity the clock speed is nonnegative. -/
theorem clockSpeed_nonneg (nu K : ℝ) (hnu : 0 < nu) (hK : K ≤ nu) :
    0 ≤ clockSpeed nu K := by
  unfold clockSpeed
  apply div_nonneg <;> linarith

/-- Below capacity the clock speed does not exceed `c = 1`. -/
theorem clockSpeed_le_one (nu K : ℝ) (hnu : 0 < nu) (hK : 0 ≤ K) :
    clockSpeed nu K ≤ 1 := by
  unfold clockSpeed
  rw [div_le_one hnu]
  linarith

/-- At capacity the clock stops. -/
theorem clockSpeed_at_capacity (nu : ℝ) : clockSpeed nu nu = 0 := by
  simp [clockSpeed]

/-- At capacity `g_00 = 0`. This is local; it is *not* a horizon theorem. -/
theorem g00_at_capacity (nu : ℝ) : g00 nu nu = 0 := by
  simp [g00, clockSpeed_at_capacity]

/-- The local index is at least one below capacity. -/
theorem localIndex_ge_one (nu K : ℝ) (_hnu : 0 < nu) (hK : 0 ≤ K) (hKnu : K < nu) :
    1 ≤ localIndex nu K := by
  unfold localIndex
  rw [le_div_iff₀ (by linarith)]
  linarith

end PMAction.WeakField
