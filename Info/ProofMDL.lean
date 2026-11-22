/-
  Info.ProofMDL — Pure Algorithmic Foundations of Lean 4 Proof-DAG & Term Compression
  =====================================================================================
  Formalizes tree-vs-DAG proof-term size, unreachable declaration pruning, α-renaming
  invariance of constant-reference streams via De Bruijn indices (`Info.Coding`),
  factored lemma MDL breakeven vs overhead penalties, and reflective certificate dominance.
  Zero IO, zero `import Lean`, zero `sorryAx`, zero `Lean.ofReduceBool`.
-/
import Info.Coding

namespace Info.ProofMDL

/-- Abstract syntax of Lean kernel proof expressions (`Expr` subset with De Bruijn `bvar`). -/
inductive ExprNode where
  | bvar (idx : Nat)
  | const (cid : Nat)
  | app (fn arg : ExprNode)
  | lam (ty body : ExprNode)
  | forallE (ty body : ExprNode)
  | lit (val : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Expanded AST tree node count of a kernel expression. -/
def exprTreeSize : ExprNode → Nat
  | .bvar _ => 1
  | .const _ => 1
  | .lit _ => 1
  | .app fn arg => 1 + exprTreeSize fn + exprTreeSize arg
  | .lam ty body => 1 + exprTreeSize ty + exprTreeSize body
  | .forallE ty body => 1 + exprTreeSize ty + exprTreeSize body

/-- Pre-order list of all subexpressions in `e`. -/
def exprSubterms : ExprNode → List ExprNode
  | e@(.bvar _) => [e]
  | e@(.const _) => [e]
  | e@(.lit _) => [e]
  | e@(.app fn arg) => e :: (exprSubterms fn ++ exprSubterms arg)
  | e@(.lam ty body) => e :: (exprSubterms ty ++ exprSubterms body)
  | e@(.forallE ty body) => e :: (exprSubterms ty ++ exprSubterms body)

/-- Hash-consing deduplication of structurally identical subexpressions. -/
def dedupNodes : List ExprNode → List ExprNode
  | [] => []
  | x :: xs =>
    let rest := dedupNodes xs
    if x ∈ rest then rest else x :: rest

/-- Number of distinct DAG nodes after structural sharing. -/
def exprUniqueNodes (e : ExprNode) : Nat :=
  (dedupNodes (exprSubterms e)).length

/-- Sequence of external constant references appearing in `e` (`bvar`s remain anonymous). -/
def exprConstIds : ExprNode → List Nat
  | .bvar _ => []
  | .const cid => [cid]
  | .lit _ => []
  | .app fn arg => exprConstIds fn ++ exprConstIds arg
  | .lam ty body => exprConstIds ty ++ exprConstIds body
  | .forallE ty body => exprConstIds ty ++ exprConstIds body

/-- Alpha-renaming of external constants leaving bound De Bruijn indices unchanged. -/
def renameExpr (f : Nat → Nat) : ExprNode → ExprNode
  | .bvar i => .bvar i
  | .const cid => .const (f cid)
  | .lit n => .lit n
  | .app fn arg => .app (renameExpr f fn) (renameExpr f arg)
  | .lam ty body => .lam (renameExpr f ty) (renameExpr f body)
  | .forallE ty body => .forallE (renameExpr f ty) (renameExpr f body)

private theorem exprSubterms_length_eq (e : ExprNode) :
    (exprSubterms e).length = exprTreeSize e := by
  induction e with
  | bvar _ | const _ | lit _ => rfl
  | app _ _ ihf iha =>
    simp only [exprSubterms, exprTreeSize, List.length_cons, List.length_append, ihf, iha]
    omega
  | lam _ _ iht ihb =>
    simp only [exprSubterms, exprTreeSize, List.length_cons, List.length_append, iht, ihb]
    omega
  | forallE _ _ iht ihb =>
    simp only [exprSubterms, exprTreeSize, List.length_cons, List.length_append, iht, ihb]
    omega

private theorem dedupNodes_length_le (xs : List ExprNode) :
    (dedupNodes xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [dedupNodes]
  | cons x tl ih =>
    simp only [dedupNodes]
    split
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

private theorem exprConstIds_renameExpr (f : Nat → Nat) (e : ExprNode) :
    exprConstIds (renameExpr f e) = (exprConstIds e).map f := by
  induction e with
  | bvar _ => simp [renameExpr, exprConstIds]
  | const _ => simp [renameExpr, exprConstIds]
  | lit _ => simp [renameExpr, exprConstIds]
  | app _ _ ihf iha =>
    simp only [renameExpr, exprConstIds, List.map_append, ihf, iha]
  | lam _ _ iht ihb =>
    simp only [renameExpr, exprConstIds, List.map_append, iht, ihb]
  | forallE _ _ iht ihb =>
    simp only [renameExpr, exprConstIds, List.map_append, iht, ihb]

/-- Cost-annotated declaration record for formal proof-library pruning analysis. -/
structure DeclCost where
  id : Nat
  cost : Nat
  deps : List Nat
  reachable : Bool
  deriving Repr, DecidableEq, Inhabited

def totalLibCost (lib : List DeclCost) : Nat :=
  (lib.map DeclCost.cost).sum

def pruneDeadDecls (lib : List DeclCost) : List DeclCost :=
  lib.filter DeclCost.reachable

def deadLibCost (lib : List DeclCost) : Nat :=
  ((lib.filter (fun d => !d.reachable)).map DeclCost.cost).sum

private theorem filter_live_plus_dead_eq (lib : List DeclCost) :
    totalLibCost (pruneDeadDecls lib) + deadLibCost lib = totalLibCost lib := by
  induction lib with
  | nil => simp [totalLibCost, pruneDeadDecls, deadLibCost]
  | cons d tl ih =>
    cases h : d.reachable <;>
      simp [totalLibCost, pruneDeadDecls, deadLibCost, h] at ih ⊢ <;>
      omega

def expandedProofCost (uses subSize : Nat) : Nat :=
  uses * subSize

def factoredProofCost (headerCost refCost uses : Nat) : Nat :=
  headerCost + uses * refCost

/-- 1. Every proof expression has strictly positive expanded tree size. -/
theorem exprTreeSize_pos (e : ExprNode) : 0 < exprTreeSize e := by
  cases e <;> simp [exprTreeSize] <;> omega

/-- 2. Function application strictly increases tree size over both subterms. -/
theorem exprTreeSize_app_gt (fn arg : ExprNode) :
    exprTreeSize fn < exprTreeSize (.app fn arg) ∧
      exprTreeSize arg < exprTreeSize (.app fn arg) := by
  have h1 : 0 < exprTreeSize fn := exprTreeSize_pos fn
  have h2 : 0 < exprTreeSize arg := exprTreeSize_pos arg
  simp only [exprTreeSize]
  omega

/-- 3. Hash-consed DAG node count never exceeds expanded proof-tree size. -/
theorem exprDagSize_le_treeSize (e : ExprNode) :
    exprUniqueNodes e ≤ exprTreeSize e := by
  unfold exprUniqueNodes
  rw [← exprSubterms_length_eq e]
  exact dedupNodes_length_le (exprSubterms e)

/-- 4. Dead-lemma pruning preserves monotonic cost and strictly reduces total cost
       whenever unreachable declarations have positive description length. -/
theorem dead_lemma_pruning_cost_le (lib : List DeclCost) :
    totalLibCost (pruneDeadDecls lib) ≤ totalLibCost lib ∧
      (0 < deadLibCost lib → totalLibCost (pruneDeadDecls lib) < totalLibCost lib) := by
  have h := filter_live_plus_dead_eq lib
  omega

/-- 5. Under reverse-reachability closure, pruning unreachable declarations preserves
       every dependency of every surviving reachable declaration. -/
theorem dead_lemma_pruning_preserves_deps (lib : List DeclCost)
    (hClosed : ∀ d ∈ lib, d.reachable = true → ∀ depId ∈ d.deps,
      ∃ d' ∈ lib, d'.id = depId ∧ d'.reachable = true) :
    ∀ d ∈ pruneDeadDecls lib, ∀ depId ∈ d.deps,
      ∃ d' ∈ pruneDeadDecls lib, d'.id = depId := by
  intro d hd depId hdep
  simp only [pruneDeadDecls, List.mem_filter] at hd ⊢
  obtain ⟨d', hd'Lib, hd'Id, hd'Reach⟩ := hClosed d hd.1 hd.2 depId hdep
  exact ⟨d', ⟨hd'Lib, hd'Reach⟩, hd'Id⟩

/-- 6. Proof Factoring Breakeven: extracting a subproof of size `subSize` used
       `uses` times into a lemma with header cost `headerCost` and call-site reference
       cost `refCost` strictly decreases Proof MDL once `headerCost < uses * (subSize - refCost)`. -/
theorem proof_factoring_breakeven (uses subSize headerCost refCost : Nat)
    (hGain : refCost ≤ subSize)
    (hBreak : headerCost < uses * (subSize - refCost)) :
    factoredProofCost headerCost refCost uses < expandedProofCost uses subSize := by
  unfold factoredProofCost expandedProofCost
  have hDist : uses * (subSize - refCost) + uses * refCost = uses * subSize := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hGain]
  omega

/-- 7. No-Free-Factoring Penalty: factoring a single-use subproof or overhead-heavy
       abstraction strictly inflates Proof MDL. -/
theorem proof_no_free_factoring (uses subSize headerCost refCost : Nat)
    (hStrict : (uses = 1 ∧ subSize ≤ refCost ∧ 0 < headerCost) ∨
      (uses * subSize < headerCost + uses * refCost)) :
    expandedProofCost uses subSize < factoredProofCost headerCost refCost uses := by
  unfold expandedProofCost factoredProofCost
  rcases hStrict with ⟨h1, hsr, hh⟩ | hlt
  · subst h1
    omega
  · omega

/-- 8. Reflective Certificate Dominance: once amortized across `m` instances, a verified
       meta-theorem plus compact certificates beats expanded proofs for every `n ≥ m`. -/
theorem reflective_certificate_dominance (metaCost certCost expandCost m : Nat)
    (hCert : certCost < expandCost)
    (hAmort : metaCost + m * certCost < m * expandCost) :
    metaCost + m * certCost < m * expandCost ∧
      ∀ n, m ≤ n → metaCost + n * certCost < n * expandCost := by
  refine ⟨hAmort, ?_⟩
  intro n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hAddL : (m + k) * certCost = m * certCost + k * certCost := Nat.add_mul m k certCost
  have hAddR : (m + k) * expandCost = m * expandCost + k * expandCost := Nat.add_mul m k expandCost
  have hStep : k * certCost ≤ k * expandCost := Nat.mul_le_mul_left k (Nat.le_of_lt hCert)
  omega

/-- 9. Kernel α-Renaming Invariance: any injective renaming of external constant identifiers
       yields the exact same canonical De Bruijn constant stream. -/
theorem alpha_expr_constIds_rename_invariance (f : Nat → Nat)
    (hf : ∀ a b, f a = f b → a = b) (e : ExprNode) :
    Info.Coding.deBruijnCanon (exprConstIds (renameExpr f e)) =
      Info.Coding.deBruijnCanon (exprConstIds e) := by
  rw [exprConstIds_renameExpr]
  exact Info.Coding.deBruijnCanon_map_inj f hf (exprConstIds e)

/-- 10. Proof Blueprint Lower Bound: the load-bearing core subset cost never exceeds total
        library cost, and strictly bounds it from below whenever boilerplate is present. -/
theorem proof_blueprint_core_lower_bound (lib : List DeclCost) (isCore : DeclCost → Bool) :
    totalLibCost (lib.filter isCore) ≤ totalLibCost lib ∧
      (0 < ((lib.filter (fun d => !isCore d)).map DeclCost.cost).sum →
        totalLibCost (lib.filter isCore) < totalLibCost lib) := by
  induction lib with
  | nil => simp [totalLibCost]
  | cons d tl ih =>
    cases h : isCore d <;>
      simp [totalLibCost, h] at ih ⊢ <;>
      omega

/-- Elementary node kind in a canonical hash-consed Proof-DAG table. -/
inductive DagOp where
  | leaf (tag atom : Nat)
  | unary (tag child : Nat)
  | binary (tag left right : Nat)
  deriving Repr, DecidableEq

/-- Minimal decoded AST expression reconstructed from a serialized Proof-DAG row. -/
inductive DecodedExpr where
  | atom (tag a : Nat)
  | node1 (tag : Nat) (c : DecodedExpr)
  | node2 (tag : Nat) (l r : DecodedExpr)
  deriving Repr, DecidableEq

/-- Safe total list lookup used for fuel-bounded DAG reconstruction. -/
def dagAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => dagAt? xs n

private theorem dagAt?_some_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → ∃ x, dagAt? xs i = some x
  | [], i, h => by simp at h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, n + 1, h => dagAt?_some_of_lt xs n (by simp at h; omega)

/-- Topological well-formedness for a single DAG node at row `idx`. -/
def dagOpBounded (idx : Nat) : DagOp → Prop
  | .leaf _ _ => True
  | .unary _ c => c < idx
  | .binary _ l r => l < idx ∧ r < idx

/-- Topological invariant: every row in `ops` references strictly earlier row indices. -/
def DagWellFormed (ops : List DagOp) : Prop :=
  ∀ i op, dagAt? ops i = some op → dagOpBounded i op

/-- Fuel-bounded recursive decoder from a serialized DAG table row back to a tree AST. -/
def decodeDagFuel (ops : List DagOp) : Nat → Nat → Option DecodedExpr
  | 0, _ => none
  | fuel + 1, idx =>
    match dagAt? ops idx with
    | none => none
    | some (.leaf tag a) => some (.atom tag a)
    | some (.unary tag c) =>
      match decodeDagFuel ops fuel c with
      | some ec => some (.node1 tag ec)
      | none => none
    | some (.binary tag l r) =>
      match decodeDagFuel ops fuel l, decodeDagFuel ops fuel r with
      | some el, some er => some (.node2 tag el er)
      | _, _ => none

private theorem decodeDagFuel_of_lt (ops : List DagOp) (hwf : DagWellFormed ops) :
    ∀ fuel idx, idx < fuel → idx < ops.length →
      ∃ e, decodeDagFuel ops fuel idx = some e
  | 0, _, hlt, _ => by omega
  | fuel + 1, idx, hlt, hlen => by
    obtain ⟨op, hop⟩ := dagAt?_some_of_lt ops idx hlen
    cases op with
    | leaf tag a =>
      refine ⟨.atom tag a, ?_⟩
      simp [decodeDagFuel, hop]
    | unary tag c =>
      have hcb : c < idx := hwf idx _ hop
      have hcf : c < fuel := by omega
      have hcl : c < ops.length := by omega
      obtain ⟨ec, hec⟩ := decodeDagFuel_of_lt ops hwf fuel c hcf hcl
      refine ⟨.node1 tag ec, ?_⟩
      simp [decodeDagFuel, hop, hec]
    | binary tag l r =>
      have hlr : l < idx ∧ r < idx := hwf idx _ hop
      have hlf : l < fuel := by omega
      have hrf : r < fuel := by omega
      have hll : l < ops.length := by omega
      have hrl : r < ops.length := by omega
      obtain ⟨el, hel⟩ := decodeDagFuel_of_lt ops hwf fuel l hlf hll
      obtain ⟨er, her⟩ := decodeDagFuel_of_lt ops hwf fuel r hrf hrl
      refine ⟨.node2 tag el er, ?_⟩
      simp [decodeDagFuel, hop, hel, her]

/-- 11. Well-Formed Hash-Consed DAG Completeness: any topologically ordered Proof-DAG table
        with `n` rows decodes losslessly from every valid root index in at most `n` fuel steps. -/
theorem dag_wellformed_decodes (ops : List DagOp) (hwf : DagWellFormed ops)
    (root : Nat) (hroot : root < ops.length) :
    ∃ tree, decodeDagFuel ops ops.length root = some tree :=
  decodeDagFuel_of_lt ops hwf ops.length root hroot hroot

/-- Full binary sharing diamond of depth `n`. -/
def chainApp : Nat → DecodedExpr
  | 0 => .atom 0 0
  | n + 1 =>
    let sub := chainApp n
    .node2 1 sub sub

/-- Linear `(n + 1)`-row DAG table representing `chainApp n` via hash-consed sharing. -/
def chainDag : Nat → List DagOp
  | 0 => [.leaf 0 0]
  | n + 1 => chainDag n ++ [.binary 1 n n]

/-- Unfolded AST node count of a decoded expression tree. -/
def decodedTreeSize : DecodedExpr → Nat
  | .atom _ _ => 1
  | .node1 _ c => 1 + decodedTreeSize c
  | .node2 _ l r => 1 + decodedTreeSize l + decodedTreeSize r

private theorem chainDag_length : ∀ n, (chainDag n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [chainDag, chainDag_length n]

private theorem pow2_le_chainApp : ∀ n, 2 ^ n ≤ decodedTreeSize (chainApp n)
  | 0 => by decide
  | n + 1 => by
    have ih := pow2_le_chainApp n
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    change 2 ^ (n + 1) ≤ 1 + decodedTreeSize (chainApp n) + decodedTreeSize (chainApp n)
    omega

private theorem linear_lt_pow2 : ∀ n, 3 ≤ n → n + 1 < 2 ^ n
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by decide
  | n + 4, _ => by
    have ih := linear_lt_pow2 (n + 3) (by omega)
    have hp : 2 ^ (n + 4) = 2 ^ (n + 3) * 2 := Nat.pow_succ 2 (n + 3)
    omega

/-- 12. Exponential DAG Sharing Gap: hash-consing compresses `chainApp n` to a `chainDag n`
        table of `n + 1` rows while its unfolded AST spans at least `2 ^ n` nodes. -/
theorem dag_sharing_exponential_gap (n : Nat) :
    (chainDag n).length = n + 1 ∧
      2 ^ n ≤ decodedTreeSize (chainApp n) ∧
      (3 ≤ n → (chainDag n).length < decodedTreeSize (chainApp n)) := by
  refine ⟨chainDag_length n, pow2_le_chainApp n, fun hn => ?_⟩
  have hlen : (chainDag n).length = n + 1 := chainDag_length n
  have hlin : n + 1 < 2 ^ n := linear_lt_pow2 n hn
  have htree : 2 ^ n ≤ decodedTreeSize (chainApp n) := pow2_le_chainApp n
  omega

/-- 13. Grammar/Macro Compression Breakeven: hoisting `k` occurrences of a body of cost `w`
        into a shared rule with definition overhead `h` and call reference cost `r ≤ w`
        strictly reduces total MDL iff `h + w < k * (w - r)`. -/
theorem grammar_pair_compression_breakeven (k w h r : Nat) (hrw : r ≤ w) :
    h + w + k * r < k * w ↔ h + w < k * (w - r) := by
  have hk : k * (w - r) + k * r = k * w := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hrw]
  omega

/-- 14. Columnar `.infp` Container Dominance: an `.infp` payload (`hdrCost + payloadCost`)
        strictly beats flat AST serialization `flatCost` whenever DAG deduplication
        (`flatCost - dagCost`) plus Ring-0 entropy reduction (`dagCost - payloadCost`)
        exceeds the fixed container header `hdrCost`. -/
theorem infp_container_beats_flat_ast
    (flatCost dagCost payloadCost hdrCost : Nat)
    (hdag : dagCost ≤ flatCost)
    (hinf1 : payloadCost ≤ dagCost)
    (hgain : hdrCost < (flatCost - dagCost) + (dagCost - payloadCost)) :
    hdrCost + payloadCost < flatCost := by
  omega

/-- 15. Cognitive Transparency MDL Bound (`INFO × SOUND` Bridge): given plain-language disclosure
        MDL `summaryBits` and comprehension budget `budgetBits`, a contract whose conditional
        complexity stays within `budgetBits` strictly dominates an obfuscated contract exceeding it. -/
theorem cognitive_transparency_mdl_bound
    (summaryBits fairJointBits predJointBits budgetBits : Nat)
    (hfairMono : summaryBits ≤ fairJointBits)
    (hpredMono : summaryBits ≤ predJointBits)
    (hfairBudget : fairJointBits - summaryBits ≤ budgetBits)
    (hpredObfuscated : budgetBits < predJointBits - summaryBits) :
    fairJointBits < predJointBits ∧
      (fairJointBits - summaryBits) < (predJointBits - summaryBits) := by
  omega

end Info.ProofMDL
