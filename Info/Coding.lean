/-
  Info.Coding — Pigeonhole Incompressibility, Kraft-McMillan, Bayes Mixture, KT & 32-bit E1/E2/E3
  ==================================================================================================
  Pure Lean 4 formalization (zero IO, zero sorryAx) of algorithmic information foundations:
    1. Pigeonhole Incompressibility No-Go (arbitrary n-bit strings)
    2. Kraft-McMillan Prefix-Tree Inequality
    3. Exact Solomonoff/Bayes Mixture Dominance & Krichevsky-Trofimov (KT) Recurrence
    4. Exact 32-bit E1/E2/E3 Binary Arithmetic Coder Partition & Renormalization Invariants.
-/
import Std.Tactic.BVDecide

namespace Info.Coding

/-! ## Section 1: Pigeonhole Principle & Incompressibility No-Go -/

private def swapFin {a : Nat} (i j x : Fin a) : Fin a :=
  if x = i then j else if x = j then i else x

private theorem swapFin_inj {a : Nat} (i j : Fin a) : Function.Injective (swapFin i j) := by
  intro x y h
  dsimp [swapFin] at h
  by_cases hxi : x = i <;> by_cases hyi : y = i <;>
    by_cases hxj : x = j <;> by_cases hyj : y = j <;>
    simp_all [Fin.ext_iff]

private theorem swapFin_right {a : Nat} (i j : Fin a) : swapFin i j j = i := by
  dsimp [swapFin]
  by_cases hj : j = i
  · simp [hj]
  · simp [hj]

theorem no_inj_fin_of_lt : ∀ (b a : Nat), b < a → (f : Fin a → Fin b) → ¬ Function.Injective f
  | 0, _a, hLt, f, _ => by
      have ha : 0 < _a := hLt
      exact Fin.elim0 (f ⟨0, ha⟩)
  | b + 1, a, hLt, f, hInj => by
      have haPos : 0 < a := Nat.lt_trans (Nat.zero_lt_succ b) hLt
      let a' := a - 1
      have hbLt : b < a' := by omega
      let last : Fin a := ⟨a', by omega⟩
      by_cases hHit : ∃ k : Fin a, (f k).val = b
      · obtain ⟨k, hk⟩ := hHit
        let g : Fin a → Fin (b + 1) := fun x => f (swapFin k last x)
        have hgInj : Function.Injective g := fun x y hxy =>
          swapFin_inj k last (hInj hxy)
        have hgLast : g last = ⟨b, Nat.lt_succ_self b⟩ := by
          dsimp [g]
          rw [swapFin_right k last]
          exact Fin.ext hk
        let g' : Fin a' → Fin b := fun x =>
          let fx := g ⟨x.val, by omega⟩
          ⟨fx.val, by
            have hne : (⟨x.val, by omega⟩ : Fin a) ≠ last := by
              intro hEq
              have hv : x.val = a' := congrArg Fin.val hEq
              omega
            have hNeVal : fx ≠ g last := fun hEq => hne (hgInj hEq)
            have hNotB : fx.val ≠ b := by
              intro hvb
              apply hNeVal
              apply Fin.ext
              rw [hvb, hgLast]
            have hBound := fx.isLt
            omega⟩
        have hg'Inj : Function.Injective g' := by
          intro x y hxy
          have hv : (g' x).val = (g' y).val := congrArg Fin.val hxy
          change (g ⟨x.val, by omega⟩).val = (g ⟨y.val, by omega⟩).val at hv
          have hFin : (⟨x.val, by omega⟩ : Fin a) = ⟨y.val, by omega⟩ := hgInj (Fin.ext hv)
          exact Fin.ext (congrArg (Fin.val : Fin a → Nat) hFin)
        exact no_inj_fin_of_lt b a' hbLt g' hg'Inj
      · let f' : Fin a' → Fin b := fun x =>
          let fx := f ⟨x.val, by omega⟩
          ⟨fx.val, by
            have hNotB : fx.val ≠ b := fun hvb => hHit ⟨⟨x.val, by omega⟩, hvb⟩
            have hBound := fx.isLt
            omega⟩
        have hf'Inj : Function.Injective f' := by
          intro x y hxy
          have hv : (f' x).val = (f' y).val := congrArg Fin.val hxy
          change (f ⟨x.val, by omega⟩).val = (f ⟨y.val, by omega⟩).val at hv
          have hFin : (⟨x.val, by omega⟩ : Fin a) = ⟨y.val, by omega⟩ := hInj (Fin.ext hv)
          exact Fin.ext (congrArg (Fin.val : Fin a → Nat) hFin)
        exact no_inj_fin_of_lt b a' hbLt f' hf'Inj

theorem pigeonhole_fin_nogo (a b : Nat) (hLt : b < a) (f : Fin a → Fin b) :
    ¬ Function.Injective f :=
  no_inj_fin_of_lt b a hLt f

theorem pigeonhole_bitvec_compression_nogo (n k : Nat) (hLt : k < 2 ^ n) (enc : BitVec n → Fin k) :
    ¬ Function.Injective enc := by
  intro hInj
  let g : Fin (2 ^ n) → Fin k := fun x => enc (BitVec.ofFin x)
  have hgInj : Function.Injective g := by
    intro x y hxy
    have hBv : BitVec.ofFin x = BitVec.ofFin y := hInj hxy
    exact BitVec.ofFin.inj hBv
  exact pigeonhole_fin_nogo (2 ^ n) k hLt g hgInj

def bitsToNat : List Bool → Nat
  | []      => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

theorem bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
      cases b <;> simp [bitsToNat, List.length_cons, Nat.pow_succ] <;> omega

theorem bitsToNat_inj_same_len : ∀ (xs ys : List Bool),
    xs.length = ys.length → bitsToNat xs = bitsToNat ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hLen, hVal => by
      simp only [List.length_cons] at hLen
      simp only [bitsToNat] at hVal
      have hxy : x = y := by cases x <;> cases y <;> simp at hVal ⊢ <;> omega
      subst hxy
      have hSub : bitsToNat xs = bitsToNat ys := by cases x <;> omega
      rw [bitsToNat_inj_same_len xs ys (by omega) hSub]

def shortBitsRank (bs : List Bool) : Nat :=
  (2 ^ bs.length - 1) + bitsToNat bs

theorem shortBitsRank_bound (bs : List Bool) (n : Nat) (hLen : bs.length < n) :
    shortBitsRank bs < 2 ^ n := by
  dsimp [shortBitsRank]
  have h1 : bitsToNat bs < 2 ^ bs.length := bitsToNat_lt bs
  have h2 : 2 ^ bs.length ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hPowPos : 1 ≤ 2 ^ bs.length := Nat.one_le_pow _ _ (by decide)
  have hnPos : 1 ≤ n := by omega
  have hPowN : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) (Nat.sub_add_cancel hnPos).symm
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ _ _
  omega

private theorem shortBitsRank_len_lt_right (xs ys : List Bool) (hLt : xs.length < ys.length) :
    shortBitsRank xs < shortBitsRank ys := by
  have hx : bitsToNat xs < 2 ^ xs.length := bitsToNat_lt xs
  have hPowPosX : 1 ≤ 2 ^ xs.length := Nat.one_le_pow _ _ (by decide)
  have hLe : 2 ^ xs.length * 2 ≤ 2 ^ ys.length := by
    rw [← Nat.pow_succ]
    exact Nat.pow_le_pow_right (by decide) hLt
  calc
    shortBitsRank xs = (2 ^ xs.length - 1) + bitsToNat xs := rfl
    _ < (2 ^ xs.length - 1) + 2 ^ xs.length := Nat.add_lt_add_left hx _
    _ = 2 ^ xs.length * 2 - 1 := by omega
    _ ≤ 2 ^ ys.length - 1 := Nat.sub_le_sub_right hLe 1
    _ ≤ shortBitsRank ys := Nat.le_add_right _ _

theorem shortBitsRank_inj (xs ys : List Bool) (h : shortBitsRank xs = shortBitsRank ys) :
    xs = ys := by
  by_cases hLen : xs.length = ys.length
  · dsimp [shortBitsRank] at h
    rw [hLen] at h
    have hNat : bitsToNat xs = bitsToNat ys := by omega
    exact bitsToNat_inj_same_len xs ys hLen hNat
  · by_cases hLt : xs.length < ys.length
    · exact absurd h (Nat.ne_of_lt (shortBitsRank_len_lt_right xs ys hLt))
    · have hGt : ys.length < xs.length := by omega
      exact absurd h.symm (Nat.ne_of_lt (shortBitsRank_len_lt_right ys xs hGt))

theorem no_strict_all_compressor (n : Nat) (enc : BitVec n → List Bool)
    (hInj : Function.Injective enc) (hAllShort : ∀ x : BitVec n, (enc x).length < n) :
    False := by
  have hAllStrict : ∀ x : BitVec n, shortBitsRank (enc x) < 2 ^ n - 1 := by
    intro x
    have hL := hAllShort x
    have h1 := bitsToNat_lt (enc x)
    have h2 : 2 ^ (enc x).length ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hPowPos : 1 ≤ 2 ^ (enc x).length := Nat.one_le_pow _ _ (by decide)
    have hnPos : 1 ≤ n := by omega
    have hPowN : 2 ^ n = 2 ^ (n - 1) * 2 := by
      calc
        2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) (Nat.sub_add_cancel hnPos).symm
        _ = 2 ^ (n - 1) * 2 := Nat.pow_succ _ _
    dsimp [shortBitsRank]
    omega
  let g' : BitVec n → Fin (2 ^ n - 1) := fun x => ⟨shortBitsRank (enc x), hAllStrict x⟩
  have hg'Inj : Function.Injective g' := fun x y hxy =>
    hInj (shortBitsRank_inj (enc x) (enc y) (congrArg Fin.val hxy))
  have hLt : 2 ^ n - 1 < 2 ^ n := by
    have hPos : 0 < 2 ^ n := Nat.pow_pos (by decide)
    omega
  exact pigeonhole_bitvec_compression_nogo n (2 ^ n - 1) hLt g' hg'Inj

/-! ## Section 2: Kraft-McMillan Prefix-Tree Inequality -/

inductive CodeTree where
  | leaf : CodeTree
  | node : CodeTree → CodeTree → CodeTree
  deriving Repr, DecidableEq, Inhabited

def CodeTree.maxDepth : CodeTree → Nat
  | .leaf     => 0
  | .node l r => 1 + max l.maxDepth r.maxDepth

def CodeTree.isFull : CodeTree → Bool
  | .leaf     => true
  | .node l r => l.isFull && r.isFull

def kraftNum : Nat → CodeTree → Nat
  | d, .leaf         => 2 ^ d
  | d + 1, .node l r => kraftNum d l + kraftNum d r
  | 0, .node _ _     => 0

theorem kraft_prefix_tree_bound (t : CodeTree) :
    ∀ d : Nat, t.maxDepth ≤ d → kraftNum d t ≤ 2 ^ d := by
  induction t with
  | leaf =>
      intro d _
      simp [kraftNum]
  | node l r ihl ihr =>
      intro d hd
      cases d with
      | zero =>
          simp [CodeTree.maxDepth] at hd
      | succ d' =>
          simp only [CodeTree.maxDepth] at hd
          have hl : l.maxDepth ≤ d' := by omega
          have hr : r.maxDepth ≤ d' := by omega
          have h1 := ihl d' hl
          have h2 := ihr d' hr
          simp only [kraftNum, Nat.pow_succ]
          omega

theorem kraft_full_tree_eq (t : CodeTree) :
    ∀ d : Nat, t.isFull = true → t.maxDepth ≤ d → kraftNum d t = 2 ^ d := by
  induction t with
  | leaf =>
      intro d _ _
      simp [kraftNum]
  | node l r ihl ihr =>
      intro d hFull hd
      cases d with
      | zero =>
          simp [CodeTree.maxDepth] at hd
      | succ d' =>
          simp only [CodeTree.isFull, Bool.and_eq_true] at hFull
          simp only [CodeTree.maxDepth] at hd
          have h1 := ihl d' hFull.1 (by omega)
          have h2 := ihr d' hFull.2 (by omega)
          simp only [kraftNum, Nat.pow_succ]
          omega

theorem kraft_root_branch_split (l r : CodeTree) (d : Nat)
    (hl : l.maxDepth ≤ d) (hr : r.maxDepth ≤ d) :
    kraftNum d l + kraftNum d r ≤ 2 ^ (d + 1) := by
  have h1 := kraft_prefix_tree_bound l d hl
  have h2 := kraft_prefix_tree_bound r d hr
  rw [Nat.pow_succ]
  omega

/-! ## Section 3: Exact Solomonoff/Bayes Mixture Dominance & KT Conservation -/

private theorem foldl_add_init (ms : List (Nat × Nat)) (acc : Nat) :
    ms.foldl (fun a mp => a + mp.1 * mp.2) acc =
      acc + ms.foldl (fun a mp => a + mp.1 * mp.2) 0 := by
  induction ms generalizing acc with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (acc + hd.1 * hd.2), ih (hd.1 * hd.2)]
      omega

theorem bayes_mixture_dominance_list : ∀ (ms : List (Nat × Nat)) (i : Nat) (hi : i < ms.length),
    (ms[i]).1 * (ms[i]).2 ≤ ms.foldl (fun acc mp => acc + mp.1 * mp.2) 0
  | [], _, hi => by simp at hi
  | hd :: tl, 0, _ => by
      simp only [List.getElem_cons_zero, List.foldl_cons, Nat.zero_add]
      rw [foldl_add_init]
      omega
  | hd :: tl, i + 1, hi => by
      simp only [List.getElem_cons_succ, List.foldl_cons, Nat.zero_add]
      rw [foldl_add_init]
      have hSub := bayes_mixture_dominance_list tl i (by simp at hi; omega)
      omega

theorem bayes_mixture_dominance_two (w1 w2 p1 p2 : Nat) :
    w1 * p1 ≤ w1 * p1 + w2 * p2 ∧ w2 * p2 ≤ w1 * p1 + w2 * p2 := by
  omega

theorem kt_step_conservation (a b : Nat) :
    (2 * a + 1) + (2 * b + 1) = 2 * (a + b + 1) := by
  omega

theorem kt_exchangeable_two_step (a b : Nat) :
    (2 * a + 1) * (2 * b + 1) = (2 * b + 1) * (2 * a + 1) :=
  Nat.mul_comm _ _

theorem kt_balanced_half_prob (n : Nat) :
    2 * (2 * n + 1) = 2 * (n + n + 1) := by
  omega

/-! ## Section 4: Exact 32-bit E1/E2/E3 Binary Arithmetic Coder Invariants (`bv_decide`) -/

def span48 (low high : BitVec 32) : BitVec 48 :=
  (high - low).zeroExtend 48 + 1#48

def arithMid (low high p : BitVec 32) : BitVec 32 :=
  low + (((span48 low high * p.zeroExtend 48) >>> 12).truncate 32 - 1#32)

theorem arith_split_valid_bv32 (low high p : BitVec 32)
    (hOrd : low ≤ high)
    (hSpan : 0x40000000#32 ≤ high - low)
    (hpLo : 1#32 ≤ p)
    (hpHi : p ≤ 4095#32) :
    low ≤ arithMid low high p ∧ arithMid low high p < high := by
  unfold arithMid span48
  bv_decide

theorem arith_split_partition_bv32 (low high p code : BitVec 32)
    (hOrd : low ≤ code)
    (hHi : code ≤ high)
    (hSpan : 0x40000000#32 ≤ high - low)
    (hpLo : 1#32 ≤ p)
    (hpHi : p ≤ 4095#32) :
    (code ≤ arithMid low high p ∧ low ≤ code ∧ code ≤ arithMid low high p) ∨
      (arithMid low high p + 1#32 ≤ code ∧ code ≤ high) := by
  unfold arithMid span48
  bv_decide

theorem arith_decode_recovers_bit_bv32 (low high p code : BitVec 32)
    (hLo : low ≤ code)
    (hHi : code ≤ high)
    (hSpan : 0x40000000#32 ≤ high - low)
    (hpLo : 1#32 ≤ p)
    (hpHi : p ≤ 4095#32) :
    (code ≤ arithMid low high p ↔ ¬ (arithMid low high p + 1#32 ≤ code)) := by
  unfold arithMid span48
  bv_decide

theorem arith_e1_preserve_order_bv32 (low high code : BitVec 32)
    (hLo : low ≤ code) (hHi : code ≤ high) (hLt : low < high)
    (hHalf : high < 0x80000000#32) :
    (low <<< 1) ≤ (code <<< 1) ∧
      (code <<< 1) ≤ ((high <<< 1) ||| 1#32) ∧
      (low <<< 1) < ((high <<< 1) ||| 1#32) := by
  bv_decide

theorem arith_e2_preserve_order_bv32 (low high code : BitVec 32)
    (hLo : low ≤ code) (hHi : code ≤ high) (hLt : low < high)
    (hHalf : 0x80000000#32 ≤ low) :
    ((low - 0x80000000#32) <<< 1) ≤ ((code - 0x80000000#32) <<< 1) ∧
      ((code - 0x80000000#32) <<< 1) ≤ (((high - 0x80000000#32) <<< 1) ||| 1#32) ∧
      ((low - 0x80000000#32) <<< 1) < (((high - 0x80000000#32) <<< 1) ||| 1#32) := by
  bv_decide

theorem arith_e3_preserve_order_bv32 (low high code : BitVec 32)
    (hLo : low ≤ code) (hHi : code ≤ high) (hLt : low < high)
    (hQ1 : 0x40000000#32 ≤ low)
    (hQ3 : high < 0xC0000000#32) :
    ((low - 0x40000000#32) <<< 1) ≤ ((code - 0x40000000#32) <<< 1) ∧
      ((code - 0x40000000#32) <<< 1) ≤ (((high - 0x40000000#32) <<< 1) ||| 1#32) ∧
      ((low - 0x40000000#32) <<< 1) < (((high - 0x40000000#32) <<< 1) ||| 1#32) := by
  bv_decide

/-! ## Section 5: Structural α-Canonicalization & Joint MDL Abstraction Algebra -/

/-- First-appearance De Bruijn index of an identifier token inside `xs`. -/
def firstIdx : List Nat → Nat → Nat
  | [], _ => 0
  | hd :: tl, x => if hd = x then 0 else 1 + firstIdx tl x

/-- Alpha-equivalence canonicalizer mapping each identifier to its first-appearance index. -/
def deBruijnCanon (xs : List Nat) : List Nat :=
  xs.map (firstIdx xs)

private theorem firstIdx_map_inj_on (ys : List Nat) (g : Nat → Nat) (x : Nat)
    (hInj : ∀ z ∈ ys, g z = g x → z = x) :
    firstIdx (ys.map g) (g x) = firstIdx ys x := by
  induction ys with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, firstIdx]
    by_cases h : hd = x
    · subst h
      simp
    · have hNe : g hd ≠ g x := fun he => h (hInj hd List.mem_cons_self he)
      simp only [h, hNe, ite_false]
      have hTail : ∀ z ∈ tl, g z = g x → z = x := fun z hz =>
        hInj z (List.mem_cons_of_mem hd hz)
      rw [ih hTail]

/-- First-appearance De Bruijn indices distinguish all tokens occurring in a stream. -/
theorem firstIdx_inj_on_mem (xs : List Nat) (x y : Nat)
    (hx : x ∈ xs) (hy : y ∈ xs) (h : firstIdx xs x = firstIdx xs y) : x = y := by
  induction xs with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [firstIdx] at h
    by_cases h1 : hd = x <;> by_cases h2 : hd = y
    · subst h1; exact h2
    · subst h1; simp only [ite_true, h2, ite_false] at h; omega
    · subst h2; simp only [h1, ite_false, ite_true] at h; omega
    · simp only [h1, h2, ite_false] at h
      have hx' : x ∈ tl := List.mem_of_ne_of_mem (Ne.symm h1) hx
      have hy' : y ∈ tl := List.mem_of_ne_of_mem (Ne.symm h2) hy
      exact ih hx' hy' (by omega)

/-- Renaming tokens by any injective renaming preserves the canonical De Bruijn stream exactly. -/
theorem deBruijnCanon_map_inj (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b) (xs : List Nat) :
    deBruijnCanon (xs.map f) = deBruijnCanon xs := by
  unfold deBruijnCanon
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  exact firstIdx_map_inj_on xs f x (fun z _ hfz => hf z x hfz)

/-- Repeated α-canonicalization is idempotent: canonical form is a fixed point. -/
theorem deBruijnCanon_idempotent (xs : List Nat) :
    deBruijnCanon (deBruijnCanon xs) = deBruijnCanon xs := by
  unfold deBruijnCanon
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  exact firstIdx_map_inj_on xs (firstIdx xs) x
    (fun z hz hEq => firstIdx_inj_on_mem xs z x hz hx hEq)

private theorem sum_fst_le_sum_snd (pairs : List (Nat × Nat)) (hDom : ∀ p ∈ pairs, p.1 ≤ p.2) :
    (pairs.map Prod.fst).sum ≤ (pairs.map Prod.snd).sum := by
  induction pairs with
  | nil => simp
  | cons p tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hp : p.1 ≤ p.2 := hDom p List.mem_cons_self
    have htl : (tl.map Prod.fst).sum ≤ (tl.map Prod.snd).sum :=
      ih (fun q hq => hDom q (List.mem_cons_of_mem p hq))
    omega

/-- No Free Abstraction (Occam MDL Penalty): extracting a non-trivial shared module `M`
    when instances fail to compress modulo `M` strictly worsens total description length. -/
theorem mdl_no_free_abstraction (pairs : List (Nat × Nat)) (lM : Nat)
    (hDom : ∀ p ∈ pairs, p.1 ≤ p.2) (hPos : 0 < lM) :
    (pairs.map Prod.fst).sum < lM + (pairs.map Prod.snd).sum := by
  have h := sum_fst_le_sum_snd pairs hDom
  omega

private theorem sum_save_delta (pairs : List (Nat × Nat)) (delta : Nat)
    (hSave : ∀ p ∈ pairs, p.2 + delta ≤ p.1) :
    (pairs.map Prod.snd).sum + pairs.length * delta ≤ (pairs.map Prod.fst).sum := by
  induction pairs with
  | nil => simp
  | cons p tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have hp : p.2 + delta ≤ p.1 := hSave p List.mem_cons_self
    have htl : (tl.map Prod.snd).sum + tl.length * delta ≤ (tl.map Prod.fst).sum :=
      ih (fun q hq => hSave q (List.mem_cons_of_mem p hq))
    omega

/-- Joint MDL Breakeven: extracting `M` strictly decreases total description length once the
    per-clone conditional savings `pairs.length * delta` exceed `L(M)`. -/
theorem mdl_refactor_breakeven (pairs : List (Nat × Nat)) (lM delta : Nat)
    (hSave : ∀ p ∈ pairs, p.2 + delta ≤ p.1) (hBreak : lM < pairs.length * delta) :
    lM + (pairs.map Prod.snd).sum < (pairs.map Prod.fst).sum := by
  have h := sum_save_delta pairs delta hSave
  omega

/-- Asymmetric Conditional Hierarchy Law: given the algorithmic chain rule
    `L(A) + L(B|A) = L(B) + L(A|B)`, `A` subsumes `B` (`L(B|A) < L(A|B)`) iff `L(B) < L(A)`. -/
theorem mdl_asymmetric_hierarchy (lA lB lBA lAB : Nat) (hChain : lA + lBA = lB + lAB) :
    lBA < lAB ↔ lB < lA := by
  omega

end Info.Coding
