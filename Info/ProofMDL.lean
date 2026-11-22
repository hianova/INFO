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

end Info.ProofMDL
