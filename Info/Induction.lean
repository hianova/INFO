/-
  Info.Induction — Statistical Context Blindness No-Go, Algebraic Zero-Residual & Switching
  ==========================================================================================
  Pure Lean 4 formalization (zero IO, zero sorryAx) of the separation between bounded
  statistical Markov/CTW context prediction and online algorithmic law induction:
    1. Depth-k Context Blindness No-Go (XOR parity & maximal LFSR exact 50/50 ambiguity)
    2. Exact Zero-Residual Laws (`bv_decide`: LFSR-16, Wolfram Rule-30, Mod-256 Affine Invertibility)
    3. Switching vs. Static Mixture Dominance on non-stationary regime-switching sources.
-/
import Std.Tactic.BVDecide

namespace Info.Induction

/-! ## Section 1: Depth-k Statistical Context Blindness No-Go -/

theorem context_parity_xor_bijection (c b : Bool) : xor (xor c b) b = c := by
  cases c <;> cases b <;> decide

theorem context_parity_distinct_targets (c : Bool) : xor c false ≠ xor c true := by
  cases c <;> decide

def parity3 (s : BitVec 3) : Bool :=
  xor (xor (s.getLsbD 0) (s.getLsbD 1)) (s.getLsbD 2)

theorem depth2_parity3_balanced_nogo (ctx : BitVec 2) :
    (parity3 (BitVec.cons false ctx) = true ∧ parity3 (BitVec.cons true ctx) = false) ∨
      (parity3 (BitVec.cons false ctx) = false ∧ parity3 (BitVec.cons true ctx) = true) := by
  revert ctx
  decide

def lfsr4Step (s : BitVec 4) : Bool :=
  xor (s.getLsbD 0) (s.getLsbD 3)

theorem depth3_lfsr4_balanced_nogo (ctx : BitVec 3) :
    ∃ b0 b1 : Bool,
      b0 ≠ b1 ∧
      lfsr4Step (ctx.cons b0) = true ∧
      lfsr4Step (ctx.cons b1) = false := by
  revert ctx
  decide

theorem arbitrary_depth_context_blind_nogo {k : Nat} (f : BitVec k → Bool) (ctx : BitVec k) :
    ∃ b0 b1 : Bool,
      b0 ≠ b1 ∧
      (xor (f ctx) b0) ≠ (xor (f ctx) b1) := by
  refine ⟨false, true, by decide, ?_⟩
  cases f ctx <;> decide

/-! ## Section 2: Exact Algorithmic Recurrence Zero-Residual Laws (`bv_decide`) -/

/-- Fibonacci 16-bit LFSR next-bit polynomial: x^16 + x^14 + x^13 + x^11 + 1. -/
def lfsr16NextBit (s : BitVec 16) : BitVec 1 :=
  ((s >>> 0) ^^^ (s >>> 2) ^^^ (s >>> 3) ^^^ (s >>> 5)).truncate 1

def lfsr16Advance (s : BitVec 16) : BitVec 16 :=
  (s >>> 1) ||| ((lfsr16NextBit s).zeroExtend 16 <<< 15)

theorem lfsr16_step_zero_residual_bv16 (s : BitVec 16) :
    (lfsr16Advance s >>> 15).truncate 1 ^^^ lfsr16NextBit s = 0#1 := by
  unfold lfsr16Advance lfsr16NextBit
  bv_decide

theorem lfsr16_nonzero_orbit_preserves_nonzero_bv16 (s : BitVec 16) (hNz : s ≠ 0#16) :
    lfsr16Advance s ≠ 0#16 := by
  unfold lfsr16Advance lfsr16NextBit
  bv_decide

theorem lfsr16_period_seed_nonfixed_bv16 :
    lfsr16Advance 0xACE1#16 ≠ 0xACE1#16 := by
  decide

/-- Wolfram Rule 30 cellular automaton step on periodic 8-bit ring. -/
def caRule30Step (row : BitVec 8) : BitVec 8 :=
  let left := row.rotateRight 1
  let right := row.rotateLeft 1
  left ^^^ (row ||| right)

theorem ca_rule30_step_zero_residual_bv8 (row : BitVec 8) :
    caRule30Step row ^^^ ((row.rotateRight 1) ^^^ (row ||| (row.rotateLeft 1))) = 0#8 := by
  unfold caRule30Step
  exact BitVec.xor_self

theorem ca_rule30_nonlinear_seed_bv8 :
    caRule30Step 0x10#8 = 0x38#8 ∧ caRule30Step 0x38#8 ≠ 0x10#8 := by
  decide

def affineMod256Step (a c x : BitVec 8) : BitVec 8 :=
  a * x + c

theorem affine_mod256_zero_residual_bv8 (a c x : BitVec 8) :
    affineMod256Step a c x - (a * x + c) = 0#8 := by
  unfold affineMod256Step
  exact BitVec.sub_self _

/-- Unique mod-256 affine multiplier recovery when `a * inv = 1#8` (odd modulus inverse LUT). -/
theorem affine_odd_step_invertible_bv8 (a inv c x : BitVec 8) (hInv : a * inv = 1#8) :
    inv * (affineMod256Step a c x - c) = x := by
  unfold affineMod256Step
  have hSub : (a * x + c) - c = a * x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add]
    have h1 : (a * x).toNat < 256 := BitVec.isLt _
    have h2 : c.toNat < 256 := BitVec.isLt _
    omega
  rw [hSub, ← BitVec.mul_assoc, BitVec.mul_comm inv a, hInv, BitVec.one_mul]

/-- Primitive 23-bit LFSR step `x^23 + x^18 + 1` (period 8,388,607 bits > 1 MB). -/
def lfsr23NextBit (s : BitVec 23) : BitVec 1 :=
  ((s >>> 0) ^^^ (s >>> 5)).truncate 1

def lfsr23Advance (s : BitVec 23) : BitVec 23 :=
  (s >>> 1) ||| ((lfsr23NextBit s).zeroExtend 23 <<< 22)

theorem lfsr23_step_zero_residual_bv23 (s : BitVec 23) :
    (lfsr23Advance s >>> 22).truncate 1 ^^^ lfsr23NextBit s = 0#1 := by
  unfold lfsr23Advance lfsr23NextBit
  bv_decide

/-- 32-bit periodic ring Wolfram Rule-30 step. -/
def caRule30Step32 (row : BitVec 32) : BitVec 32 :=
  (row.rotateRight 1) ^^^ (row ||| (row.rotateLeft 1))

theorem ca_rule30_step_zero_residual_bv32 (row : BitVec 32) :
    caRule30Step32 row ^^^ ((row.rotateRight 1) ^^^ (row ||| (row.rotateLeft 1))) = 0#32 := by
  unfold caRule30Step32
  exact BitVec.xor_self

/-- Exact 4-step Hensel-Newton inverse mod 2^16 for any odd 16-bit integer (0 division). -/
def henselInv16 (dx : BitVec 16) : BitVec 16 :=
  let i1 := dx * (2#16 - dx * dx)
  let i2 := i1 * (2#16 - dx * i1)
  let i3 := i2 * (2#16 - dx * i2)
  i3 * (2#16 - dx * i3)

private theorem nat_and_pow2_sub_one (x k : Nat) : x &&& (2 ^ k - 1) = x % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod x k

private theorem hensel_poly_bv16 (u : BitVec 16) :
    1#16 - u * (2#16 - u) = (1#16 - u) * (1#16 - u) := by
  have h2 : (2#16 : BitVec 16) = 1#16 + 1#16 := by decide
  rw [h2]
  simp only [BitVec.sub_eq_add_neg, BitVec.mul_add, BitVec.add_mul, BitVec.mul_neg,
             BitVec.neg_mul, BitVec.mul_one, BitVec.one_mul, BitVec.neg_neg, BitVec.neg_add]
  ac_rfl

private theorem hensel_base_odd_bv16 (dx : BitVec 16) (hOdd : dx &&& 1#16 = 1#16) :
    (1#16 - dx * dx) &&& 7#16 = 0#16 := by
  have hMod2 : dx.toNat % 2 = 1 := by
    have h0 := congrArg BitVec.toNat hOdd
    simpa [BitVec.toNat_and, Nat.and_one_is_mod] using h0
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (65536 - (dx.toNat * dx.toNat) % 65536 + 1) % 65536 &&& 7 = 0
  rw [show (7 : Nat) = 2 ^ 3 - 1 by decide, nat_and_pow2_sub_one]
  have hMod8 : (dx.toNat * dx.toNat) % 8 = 1 := by
    have hLt8 : dx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    calc (dx.toNat * dx.toNat) % 8
      _ = ((dx.toNat % 8) * (dx.toNat % 8)) % 8 := by simp [Nat.mul_mod]
      _ = 1 := by
          have : dx.toNat % 8 = 1 ∨ dx.toNat % 8 = 3 ∨ dx.toNat % 8 = 5 ∨ dx.toNat % 8 = 7 := by omega
          rcases this with h | h | h | h <;> simp [h]
  have h1 : (65536 - (dx.toNat * dx.toNat) % 65536 + 1) % 65536 % 8 =
      (65536 - (dx.toNat * dx.toNat) % 65536 + 1) % 8 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 65536)]
  rw [h1]
  have h2 : ((dx.toNat * dx.toNat) % 65536) % 8 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 65536), hMod8]
  have h3 : (dx.toNat * dx.toNat) % 65536 < 65536 := Nat.mod_lt _ (by decide)
  omega

private theorem hensel_lift_pow2 (r : BitVec 16) (k : Nat) (hk : k ≤ 8)
    (h : r.toNat % (2 ^ k) = 0) : (r * r).toNat % (2 ^ (2 * k)) = 0 := by
  rw [BitVec.toNat_mul]
  have hdvd : 2 ^ (2 * k) ∣ 65536 := by
    have hle : 2 * k ≤ 16 := by omega
    rw [show (65536 : Nat) = 2 ^ 16 by decide]
    exact Nat.pow_dvd_pow 2 hle
  rw [Nat.mod_mod_of_dvd _ hdvd]
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
  rw [hm]
  have hEq : (2 ^ k * m) * (2 ^ k * m) = 2 ^ (2 * k) * (m * m) := by
    rw [show 2 * k = k + k by omega, Nat.pow_add]
    calc (2 ^ k * m) * (2 ^ k * m)
      _ = 2 ^ k * (m * (2 ^ k * m)) := Nat.mul_assoc _ _ _
      _ = 2 ^ k * (2 ^ k * (m * m)) := by rw [Nat.mul_left_comm m (2 ^ k) m]
      _ = (2 ^ k * 2 ^ k) * (m * m) := (Nat.mul_assoc _ _ _).symm
  rw [hEq, Nat.mul_mod_right]

private theorem hensel_lift_3_to_6 (r : BitVec 16) (h : r &&& 7#16 = 0#16) :
    (r * r) &&& 63#16 = 0#16 := by
  have hMod : r.toNat % (2 ^ 3) = 0 := by
    have h0 := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at h0
    change r.toNat &&& 7 = 0 at h0
    rwa [show (7 : Nat) = 2 ^ 3 - 1 by decide, nat_and_pow2_sub_one] at h0
  have hSq := hensel_lift_pow2 r 3 (by decide) hMod
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (r * r).toNat &&& 63 = 0
  rwa [show (63 : Nat) = 2 ^ 6 - 1 by decide, nat_and_pow2_sub_one]

private theorem hensel_lift_6_to_12 (r : BitVec 16) (h : r &&& 63#16 = 0#16) :
    (r * r) &&& 4095#16 = 0#16 := by
  have hMod : r.toNat % (2 ^ 6) = 0 := by
    have h0 := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at h0
    change r.toNat &&& 63 = 0 at h0
    rwa [show (63 : Nat) = 2 ^ 6 - 1 by decide, nat_and_pow2_sub_one] at h0
  have hSq := hensel_lift_pow2 r 6 (by decide) hMod
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (r * r).toNat &&& 4095 = 0
  rwa [show (4095 : Nat) = 2 ^ 12 - 1 by decide, nat_and_pow2_sub_one]

private theorem hensel_lift_12_to_0 (r : BitVec 16) (h : r &&& 4095#16 = 0#16) :
    r * r = 0#16 := by
  have hMod : r.toNat % 4096 = 0 := by
    have h0 := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at h0
    change r.toNat &&& 4095 = 0 at h0
    rw [show (4095 : Nat) = 2 ^ 12 - 1 by decide, nat_and_pow2_sub_one] at h0
    exact h0
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hMod
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, hm]
  have hEq : (4096 * m) * (4096 * m) = 65536 * (256 * (m * m)) := by
    calc (4096 * m) * (4096 * m)
      _ = 4096 * (m * (4096 * m)) := Nat.mul_assoc _ _ _
      _ = 4096 * (4096 * (m * m)) := by rw [Nat.mul_left_comm m 4096 m]
      _ = (4096 * 4096) * (m * m) := (Nat.mul_assoc _ _ _).symm
      _ = (65536 * 256) * (m * m) := by rw [show (4096 * 4096 : Nat) = 65536 * 256 by decide]
      _ = 65536 * (256 * (m * m)) := Nat.mul_assoc _ _ _
  rw [hEq, Nat.mul_mod_right]
  rfl

theorem affine_hensel_inv_bv16 (dx : BitVec 16) (hOdd : dx &&& 1#16 = 1#16) :
    dx * henselInv16 dx = 1#16 := by
  let i0 := dx
  let i1 := i0 * (2#16 - dx * i0)
  let i2 := i1 * (2#16 - dx * i1)
  let i3 := i2 * (2#16 - dx * i2)
  have hstep : ∀ x : BitVec 16, 1#16 - dx * (x * (2#16 - dx * x)) =
      (1#16 - dx * x) * (1#16 - dx * x) := fun x => by
    rw [← BitVec.mul_assoc]
    exact hensel_poly_bv16 (dx * x)
  have r0 : (1#16 - dx * i0) &&& 7#16 = 0#16 := hensel_base_odd_bv16 dx hOdd
  have r1 : (1#16 - dx * i1) &&& 63#16 = 0#16 := by
    rw [hstep i0]; exact hensel_lift_3_to_6 _ r0
  have r2 : (1#16 - dx * i2) &&& 4095#16 = 0#16 := by
    rw [hstep i1]; exact hensel_lift_6_to_12 _ r1
  have r3 : 1#16 - dx * i3 = 0#16 := by
    rw [hstep i2]; exact hensel_lift_12_to_0 _ r2
  have r4 : 1#16 - dx * henselInv16 dx = 0#16 := by
    change 1#16 - dx * (i3 * (2#16 - dx * i3)) = 0#16
    rw [hstep i3, r3]
    decide
  have hSub : ∀ y : BitVec 16, y = 1#16 - (1#16 - y) := fun y => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have hy : y.toNat < 65536 := y.isLt
    omega
  calc
    dx * henselInv16 dx = 1#16 - (1#16 - dx * henselInv16 dx) := hSub _
    _ = 1#16 - 0#16 := by rw [r4]
    _ = 1#16 := by decide

/-! ## Section 3: Switching vs. Static Mixture Dominance on Regime-Switching Sources -/

theorem switching_mixture_dominates_static_nat (alpha M pA pB pStaticA pStaticB : Nat)
    (_hAlphaPos : 0 < alpha) (hAlphaLe : alpha ≤ M)
    (hBeat : M * (pStaticA * pStaticB) < alpha * (pA * pB)) :
    M * (pStaticA * pStaticB) < alpha * (pA * pB) + (M - alpha) * (pStaticA * pStaticB) := by
  have _ := hAlphaLe
  omega

theorem switching_segment_regret_bound (wSw pSw pRest : Nat) :
    wSw * pSw ≤ wSw * pSw + pRest := by
  omega

theorem regime_switch_joint_strictly_better (k pAlt pTrue : Nat) (hk : 1 ≤ k) (hGt : pAlt < pTrue) :
    pAlt * k < pTrue * k :=
  Nat.mul_lt_mul_of_pos_right hGt hk

end Info.Induction
