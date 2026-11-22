/-
  Info.Bounds — Discrete DPI Contraction, Sphere Packing / Singleton & Zero-FP Integer LP Duality
  ================================================================================================
  Pure Lean 4 formalization (zero IO, zero sorryAx) of information & coding capacity bounds:
    1. Exact L1 / Total-Variation Data Processing Inequality (2x2, 3x3 & iterated channels)
    2. Singleton Projection Bound (via Pigeonhole) & Perfect Sphere Packing ([7,4,3], [23,12,7])
    3. Zero-FP-Trust Integer Linear Programming Weak Duality & Delsarte Dual Soundness.
-/
import Info.Coding

namespace Info.Bounds

/-! ## Section 1: Discrete Data Processing Inequality (L1 Contraction) -/

def absDiff (x y : Nat) : Nat :=
  if x ≤ y then y - x else x - y

theorem absDiff_comm (x y : Nat) : absDiff x y = absDiff y x := by
  dsimp [absDiff]
  by_cases h1 : x ≤ y <;> by_cases h2 : y ≤ x <;> simp [h1, h2] <;> omega

theorem absDiff_add_le (a b c d : Nat) :
    absDiff (a + b) (c + d) ≤ absDiff a c + absDiff b d := by
  dsimp [absDiff]
  split <;> split <;> split <;> omega

theorem absDiff_mul_left (k x y : Nat) :
    absDiff (k * x) (k * y) = k * absDiff x y := by
  dsimp [absDiff]
  by_cases h : x ≤ y
  · have hk : k * x ≤ k * y := Nat.mul_le_mul_left k h
    simp [h, hk, Nat.mul_sub_left_distrib]
  · cases k with
    | zero => simp
    | succ k' =>
        have hyx : y ≤ x := by omega
        have hk : (k' + 1) * y ≤ (k' + 1) * x := Nat.mul_le_mul_left (k' + 1) hyx
        have hNot : ¬ ((k' + 1) * x ≤ (k' + 1) * y) := by
          intro hle
          exact h (Nat.le_of_mul_le_mul_left hle (Nat.zero_lt_succ k'))
        have _ := hk
        simp [h, hNot, Nat.mul_sub_left_distrib]

theorem dpi_l1_contraction_2x2
    (S k00 k01 k10 k11 p0 p1 q0 q1 : Nat)
    (hRow0 : k00 + k01 = S)
    (hRow1 : k10 + k11 = S) :
    absDiff (k00 * p0 + k10 * p1) (k00 * q0 + k10 * q1) +
      absDiff (k01 * p0 + k11 * p1) (k01 * q0 + k11 * q1)
      ≤ S * (absDiff p0 q0 + absDiff p1 q1) := by
  have h1 := absDiff_add_le (k00 * p0) (k10 * p1) (k00 * q0) (k10 * q1)
  have h2 := absDiff_add_le (k01 * p0) (k11 * p1) (k01 * q0) (k11 * q1)
  rw [absDiff_mul_left k00 p0 q0, absDiff_mul_left k10 p1 q1] at h1
  rw [absDiff_mul_left k01 p0 q0, absDiff_mul_left k11 p1 q1] at h2
  have hSum : (k00 + k01) * absDiff p0 q0 + (k10 + k11) * absDiff p1 q1 =
      S * (absDiff p0 q0 + absDiff p1 q1) := by
    rw [hRow0, hRow1, Nat.mul_add]
  have hExpand :
      (k00 * absDiff p0 q0 + k10 * absDiff p1 q1) +
        (k01 * absDiff p0 q0 + k11 * absDiff p1 q1) =
        (k00 + k01) * absDiff p0 q0 + (k10 + k11) * absDiff p1 q1 := by
    rw [Nat.add_mul, Nat.add_mul]
    omega
  omega

theorem dpi_l1_contraction_3x3
    (S k00 k01 k02 k10 k11 k12 k20 k21 k22 p0 p1 p2 q0 q1 q2 : Nat)
    (hRow0 : k00 + k01 + k02 = S)
    (hRow1 : k10 + k11 + k12 = S)
    (hRow2 : k20 + k21 + k22 = S) :
    absDiff (k00 * p0 + k10 * p1 + k20 * p2) (k00 * q0 + k10 * q1 + k20 * q2) +
      absDiff (k01 * p0 + k11 * p1 + k21 * p2) (k01 * q0 + k11 * q1 + k21 * q2) +
      absDiff (k02 * p0 + k12 * p1 + k22 * p2) (k02 * q0 + k12 * q1 + k22 * q2)
      ≤ S * (absDiff p0 q0 + absDiff p1 q1 + absDiff p2 q2) := by
  have tri := fun x0 x1 x2 y0 y1 y2 : Nat =>
    calc
      absDiff (x0 + x1 + x2) (y0 + y1 + y2)
          ≤ absDiff (x0 + x1) (y0 + y1) + absDiff x2 y2 := absDiff_add_le (x0 + x1) x2 (y0 + y1) y2
      _ ≤ absDiff x0 y0 + absDiff x1 y1 + absDiff x2 y2 := Nat.add_le_add_right (absDiff_add_le x0 x1 y0 y1) _
  have h0 := tri (k00 * p0) (k10 * p1) (k20 * p2) (k00 * q0) (k10 * q1) (k20 * q2)
  have h1 := tri (k01 * p0) (k11 * p1) (k21 * p2) (k01 * q0) (k11 * q1) (k21 * q2)
  have h2 := tri (k02 * p0) (k12 * p1) (k22 * p2) (k02 * q0) (k12 * q1) (k22 * q2)
  simp only [absDiff_mul_left] at h0 h1 h2
  have hSum : (k00 + k01 + k02) * absDiff p0 q0 +
      (k10 + k11 + k12) * absDiff p1 q1 +
      (k20 + k21 + k22) * absDiff p2 q2 =
      S * (absDiff p0 q0 + absDiff p1 q1 + absDiff p2 q2) := by
    rw [hRow0, hRow1, hRow2, Nat.mul_add, Nat.mul_add]
  have hAlg :
      (k00 * absDiff p0 q0 + k10 * absDiff p1 q1 + k20 * absDiff p2 q2) +
        (k01 * absDiff p0 q0 + k11 * absDiff p1 q1 + k21 * absDiff p2 q2) +
        (k02 * absDiff p0 q0 + k12 * absDiff p1 q1 + k22 * absDiff p2 q2) =
        (k00 + k01 + k02) * absDiff p0 q0 +
        (k10 + k11 + k12) * absDiff p1 q1 +
        (k20 + k21 + k22) * absDiff p2 q2 := by
    simp only [Nat.add_mul]
    omega
  omega

theorem dpi_two_step_contraction_2x2
    (S1 S2 k00 k01 k10 k11 m00 m01 m10 m11 p0 p1 q0 q1 : Nat)
    (hK0 : k00 + k01 = S1) (hK1 : k10 + k11 = S1)
    (hM0 : m00 + m01 = S2) (hM1 : m10 + m11 = S2) :
    let u0 := k00 * p0 + k10 * p1
    let u1 := k01 * p0 + k11 * p1
    let v0 := k00 * q0 + k10 * q1
    let v1 := k01 * q0 + k11 * q1
    absDiff (m00 * u0 + m10 * u1) (m00 * v0 + m10 * v1) +
      absDiff (m01 * u0 + m11 * u1) (m01 * v0 + m11 * v1)
      ≤ S2 * (S1 * (absDiff p0 q0 + absDiff p1 q1)) := by
  intro u0 u1 v0 v1
  have step1 := dpi_l1_contraction_2x2 S1 k00 k01 k10 k11 p0 p1 q0 q1 hK0 hK1
  have step2 := dpi_l1_contraction_2x2 S2 m00 m01 m10 m11 u0 u1 v0 v1 hM0 hM1
  exact Nat.le_trans step2 (Nat.mul_le_mul_left S2 step1)

/-! ## Section 2: Singleton Bound & Perfect Hamming/Golay Sphere Packing -/

theorem singleton_binary_nogo (n d M : Nat) (hd : 1 ≤ d) (hn : d - 1 ≤ n)
    (hGt : 2 ^ (n - (d - 1)) < M) (proj : Fin M → BitVec (n - (d - 1))) :
    ¬ Function.Injective proj := by
  have _ := hd
  have _ := hn
  intro hInj
  let g : Fin M → Fin (2 ^ (n - (d - 1))) := fun i => (proj i).toFin
  have hgInj : Function.Injective g := by
    intro x y hxy
    have hv : (proj x).toNat = (proj y).toNat := congrArg Fin.val hxy
    exact hInj (BitVec.eq_of_toNat_eq hv)
  exact Info.Coding.pigeonhole_fin_nogo M (2 ^ (n - (d - 1))) hGt g hgInj

theorem hamming_7_4_perfect_packing :
    (2 ^ 4) * (1 + 7) = 2 ^ 7 := by
  decide

theorem golay_23_12_perfect_packing :
    (2 ^ 12) * (1 + 23 + 253 + 1771) = 2 ^ 23 := by
  decide

/-! ## Section 3: Zero-FP-Trust Integer LP Weak Duality & Delsarte Dual Soundness -/

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _     => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_nonneg : ∀ (n : Nat) (f : Fin n → Int),
    (∀ i, 0 ≤ f i) → 0 ≤ sumFin n f
  | 0, _, _ => Int.le_refl 0
  | n + 1, f, hf => by
      have h1 := sumFin_nonneg n (fun i => f i.castSucc) (fun i => hf i.castSucc)
      have h2 := hf ⟨n, Nat.lt_succ_self n⟩
      dsimp [sumFin]
      omega

theorem sumFin_mono : ∀ (n : Nat) (f g : Fin n → Int),
    (∀ i, f i ≤ g i) → sumFin n f ≤ sumFin n g
  | 0, _, _, _ => Int.le_refl 0
  | n + 1, f, g, hfg => by
      have h1 := sumFin_mono n (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => hfg i.castSucc)
      have h2 := hfg ⟨n, Nat.lt_succ_self n⟩
      dsimp [sumFin]
      omega

theorem sumFin_mul_right : ∀ (n : Nat) (f : Fin n → Int) (c : Int),
    sumFin n (fun i => f i * c) = sumFin n f * c
  | 0, _, c => by simp [sumFin]
  | n + 1, f, c => by
      dsimp [sumFin]
      rw [sumFin_mul_right n (fun i => f i.castSucc) c, Int.add_mul]

theorem sumFin_mul_left : ∀ (n : Nat) (c : Int) (f : Fin n → Int),
    sumFin n (fun i => c * f i) = c * sumFin n f
  | 0, c, _ => by simp [sumFin]
  | n + 1, c, f => by
      dsimp [sumFin]
      rw [sumFin_mul_left n c (fun i => f i.castSucc), Int.mul_add]

theorem sumFin_add : ∀ (n : Nat) (f g : Fin n → Int),
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g
  | 0, _, _ => by simp [sumFin]
  | n + 1, f, g => by
      dsimp [sumFin]
      rw [sumFin_add n (fun i => f i.castSucc) (fun i => g i.castSucc)]
      omega

theorem sumFin_swap : ∀ (m n : Nat) (h : Fin m → Fin n → Int),
    sumFin m (fun i => sumFin n (fun j => h i j)) =
      sumFin n (fun j => sumFin m (fun i => h i j))
  | 0, n, h => by
      dsimp [sumFin]
      clear h
      induction n with
      | zero => rfl
      | succ n ih =>
          change (0 : Int) = sumFin n (fun _ => (0 : Int)) + 0
          rw [← ih]
          rfl
  | m + 1, n, h => by
      dsimp [sumFin]
      rw [sumFin_swap m n (fun i j => h i.castSucc j)]
      rw [← sumFin_add]

theorem lp_weak_duality_int (m n : Nat)
    (A : Fin m → Fin n → Int)
    (b : Fin m → Int)
    (c : Fin n → Int)
    (x : Fin n → Int)
    (y : Fin m → Int)
    (hxNonneg : ∀ j, 0 ≤ x j)
    (hyNonneg : ∀ i, 0 ≤ y i)
    (hPrimal : ∀ i, sumFin n (fun j => A i j * x j) ≤ b i)
    (hDual : ∀ j, c j ≤ sumFin m (fun i => y i * A i j)) :
    sumFin n (fun j => c j * x j) ≤ sumFin m (fun i => y i * b i) := by
  have hStep1 : sumFin n (fun j => c j * x j) ≤
      sumFin n (fun j => sumFin m (fun i => y i * A i j) * x j) := by
    apply sumFin_mono
    intro j
    exact Int.mul_le_mul_of_nonneg_right (hDual j) (hxNonneg j)
  have hStep2Eq : sumFin n (fun j => sumFin m (fun i => y i * A i j) * x j) =
      sumFin m (fun i => y i * sumFin n (fun j => A i j * x j)) := by
    calc
      sumFin n (fun j => sumFin m (fun i => y i * A i j) * x j)
          = sumFin n (fun j => sumFin m (fun i => (y i * A i j) * x j)) := by
              congr 1; funext j; exact (sumFin_mul_right m (fun i => y i * A i j) (x j)).symm
      _ = sumFin m (fun i => sumFin n (fun j => (y i * A i j) * x j)) :=
          sumFin_swap n m (fun j i => (y i * A i j) * x j)
      _ = sumFin m (fun i => sumFin n (fun j => y i * (A i j * x j))) := by
          congr 1; funext i; congr 1; funext j; exact Int.mul_assoc (y i) (A i j) (x j)
      _ = sumFin m (fun i => y i * sumFin n (fun j => A i j * x j)) := by
          congr 1; funext i; exact sumFin_mul_left n (y i) (fun j => A i j * x j)
  have hStep3 : sumFin m (fun i => y i * sumFin n (fun j => A i j * x j)) ≤
      sumFin m (fun i => y i * b i) := by
    apply sumFin_mono
    intro i
    exact Int.mul_le_mul_of_nonneg_left (hPrimal i) (hyNonneg i)
  omega

private theorem sumFin_head_of_tail_nonpos (n : Nat) (hn : 0 < n) (f : Fin n → Int)
    (hTail : ∀ j : Fin n, j.val ≠ 0 → f j ≤ 0) :
    ∀ m : Nat, 1 ≤ m → (hm : m ≤ n) →
      sumFin m (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ≤ f ⟨0, hn⟩ := by
  intro m hm1 hmn
  induction m with
  | zero => omega
  | succ m' ih =>
      cases m' with
      | zero =>
          simp [sumFin]
      | succ m'' =>
          have hPrev := ih (Nat.succ_pos m'') (Nat.le_of_succ_le hmn)
          have hLast : f ⟨m'' + 1, hmn⟩ ≤ 0 := hTail ⟨m'' + 1, hmn⟩ (Nat.succ_ne_zero m'')
          have hStep : sumFin (m'' + 2) (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩) =
              sumFin (m'' + 1) (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_succ_le hmn)⟩) +
                f ⟨m'' + 1, hmn⟩ := rfl
          rw [hStep]
          exact Int.le_trans (Int.add_le_add hPrev hLast) (Int.le_of_eq (Int.add_zero _))

/-- Delsarte LP Dual Soundness for binary code size `A(n, d)`:
    Given distance distribution `a : Fin n → Int` (`a 0 ≤ 1`, and for `j ≥ 1`, either `a j = 0`
    or `lam j ≤ 0`, so `a j * lam j ≤ 0`), nonnegative dual multipliers `y : Fin n → Int`,
    and MacWilliams nonnegativity `0 ≤ ∑_j a_j K k j`, with `lam j = c0 + ∑_k y_k K k j`,
    the total code size satisfies `c0 * ∑_j a_j ≤ lam 0`. Zero-FP-Trust unconditional proof. -/
theorem delsarte_dual_certificate_sound (n : Nat) (hn : 0 < n)
    (a : Fin n → Int) (K : Fin n → Fin n → Int) (y : Fin n → Int) (c0 : Int)
    (hA0 : a ⟨0, hn⟩ ≤ 1)
    (hYNonneg : ∀ k, 0 ≤ y k)
    (hMacWilliams : ∀ k, 0 ≤ sumFin n (fun j => a j * K k j))
    (hSlack : ∀ j, j.val ≠ 0 → a j * (c0 + sumFin n (fun k => y k * K k j)) ≤ 0)
    (hLam0Pos : 0 ≤ c0 + sumFin n (fun k => y k * K k ⟨0, hn⟩)) :
    c0 * sumFin n a ≤ c0 + sumFin n (fun k => y k * K k ⟨0, hn⟩) := by
  let lam : Fin n → Int := fun j => c0 + sumFin n (fun k => y k * K k j)
  have hLowerTerm : ∀ k, 0 ≤ y k * sumFin n (fun j => a j * K k j) := fun k =>
    Int.mul_nonneg (hYNonneg k) (hMacWilliams k)
  have hDoubleNonneg : 0 ≤ sumFin n (fun k => y k * sumFin n (fun j => a j * K k j)) :=
    sumFin_nonneg n _ hLowerTerm
  have hSwapEq : sumFin n (fun j => a j * sumFin n (fun k => y k * K k j)) =
      sumFin n (fun k => y k * sumFin n (fun j => a j * K k j)) := by
    calc
      sumFin n (fun j => a j * sumFin n (fun k => y k * K k j))
          = sumFin n (fun j => sumFin n (fun k => a j * (y k * K k j))) := by
              congr 1; funext j; exact (sumFin_mul_left n (a j) (fun k => y k * K k j)).symm
      _ = sumFin n (fun k => sumFin n (fun j => a j * (y k * K k j))) :=
          sumFin_swap n n (fun j k => a j * (y k * K k j))
      _ = sumFin n (fun k => sumFin n (fun j => y k * (a j * K k j))) := by
          congr 1; funext k; congr 1; funext j; exact Int.mul_left_comm (a j) (y k) (K k j)
      _ = sumFin n (fun k => y k * sumFin n (fun j => a j * K k j)) := by
          congr 1; funext k; exact sumFin_mul_left n (y k) (fun j => a j * K k j)
  have hSumALamLower : c0 * sumFin n a ≤ sumFin n (fun j => a j * lam j) := by
    have hDist : sumFin n (fun j => a j * lam j) =
        c0 * sumFin n a + sumFin n (fun j => a j * sumFin n (fun k => y k * K k j)) := by
      have h1 : sumFin n (fun j => a j * lam j) =
          sumFin n (fun j => a j * c0 + a j * sumFin n (fun k => y k * K k j)) := by
        congr 1; funext j; dsimp [lam]; exact Int.mul_add (a j) c0 _
      rw [h1, sumFin_add, sumFin_mul_right, Int.mul_comm (sumFin n a) c0]
    omega
  have hSumALamUpper : sumFin n (fun j => a j * lam j) ≤ a ⟨0, hn⟩ * lam ⟨0, hn⟩ :=
    sumFin_head_of_tail_nonpos n hn (fun j => a j * lam j) hSlack n hn (Nat.le_refl n)
  have hHead : a ⟨0, hn⟩ * lam ⟨0, hn⟩ ≤ lam ⟨0, hn⟩ := by
    have h1 : a ⟨0, hn⟩ * lam ⟨0, hn⟩ ≤ 1 * lam ⟨0, hn⟩ :=
      Int.mul_le_mul_of_nonneg_right hA0 hLam0Pos
    rw [Int.one_mul] at h1
    exact h1
  exact Int.le_trans hSumALamLower (Int.le_trans hSumALamUpper hHead)

end Info.Bounds
