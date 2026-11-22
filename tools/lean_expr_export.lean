/-
  tools/lean_expr_export.lean — Lean 4 Kernel Proof-Term DAG & Token Exporter
  ============================================================================
  Imports compiled `.olean` modules directly via `Lean.importModules`, walks each
  declaration's kernel `Expr` (`type` + `value`) in O(|DAG|) using memoized subterm
  sharing, computes tree vs DAG node counts, exact in-prefix dependencies, axiom tags,
  and bounded De Bruijn `INFO_LANG_LEAN_EXPR` token streams for `build/info`.

  Usage:
    lean --run tools/lean_expr_export.lean <ModuleName> <RootPrefix> <OutJson> [searchPath...]
-/
import Lean

open Lean

namespace LeanExprExport

def satCap : Nat := 1000000000
def maxTokens : Nat := 1536

def satAdd (a b : Nat) : Nat :=
  let s := a + b
  if s > satCap then satCap else s

def jsonEscape (s : String) : String :=
  Id.run do
    let mut out := ""
    for ch in s.toList do
      if ch == '\\' then out := out ++ "\\\\"
      else if ch == '"' then out := out ++ "\\\""
      else if ch == '\n' then out := out ++ "\\n"
      else if ch == '\r' then out := out ++ "\\r"
      else if ch == '\t' then out := out ++ "\\t"
      else out := out.push ch
    return out

def isInternalDecl (s : String) : Bool :=
  let parts := ["_cstage", "_boxed", "_sunfold", "._unsafe_rec", ".match_",
    ".eq_", ".rec", ".casesOn", ".noConfusion", ".below", ".brecOn", ".sizeOf_spec"]
  parts.any fun pat => (s.splitOn pat).length > 1

def matchesPrefix (s rootPrefix : String) : Bool :=
  s == rootPrefix || s.startsWith (rootPrefix ++ ".")

def isKnownAxiom (s : String) : Bool :=
  s == "propext" || s == "Classical.choice" || s == "Quot.sound" ||
    s == "sorryAx" || s == "Lean.ofReduceBool" || s == "Lean.trustCompiler"

def isPreservedKernelConst (s : String) : Option String :=
  if s == "Eq" then some "EQ"
  else if s == "And" then some "AND"
  else if s == "Or" then some "OR"
  else if s == "Not" then some "NOT"
  else if s == "Nat" then some "NAT"
  else if s == "Int" then some "INT"
  else if s == "BitVec" then some "BVEC"
  else none

structure WalkState where
  rootPrefix : String
  selfName : String
  memo : Std.HashMap Expr (Nat × Nat) := {}
  nextId : Nat := 0
  dagNodes : Nat := 0
  deps : Std.HashSet String := {}
  axioms : Std.HashSet String := {}
  tokens : Array String := #[]

def pushTok (st : WalkState) (tok : String) : WalkState :=
  if st.tokens.size < maxTokens then { st with tokens := st.tokens.push tok } else st

partial def walkExpr (e : Expr) (st : WalkState) : (Nat × Nat) × WalkState :=
  match st.memo[e]? with
  | some (nid, tsz) =>
    let st' := pushTok st s!"REF{nid}"
    ((nid, tsz), st')
  | none =>
    let ((tsz), st1) :=
      match e with
      | .bvar idx =>
        let st' := pushTok st s!"BV{idx}"
        (1, st')
      | .fvar _ =>
        let st' := pushTok st "FV"
        (1, st')
      | .mvar _ =>
        let st' := pushTok st "MV"
        (1, st')
      | .sort lvl =>
        let tag := match lvl with | .zero => "PROP" | _ => "TYPE"
        let st' := pushTok st tag
        (1, st')
      | .const nm _ =>
        let s := nm.toString
        let stA :=
          if isKnownAxiom s then { st with axioms := st.axioms.insert s } else st
        let stD :=
          if s != stA.selfName && matchesPrefix s stA.rootPrefix && !isInternalDecl s then
            { stA with deps := stA.deps.insert s }
          else stA
        let tok := match isPreservedKernelConst s with
          | some kw => kw
          | none => s!"C_{s}"
        let stT := pushTok stD tok
        (1, stT)
      | .app fn arg =>
        let st0 := pushTok st "AP"
        let ((_, s1), st1) := walkExpr fn st0
        let ((_, s2), st2) := walkExpr arg st1
        (satAdd 1 (satAdd s1 s2), st2)
      | .lam _ ty body _ =>
        let st0 := pushTok st "LM"
        let ((_, s1), st1) := walkExpr ty st0
        let ((_, s2), st2) := walkExpr body st1
        (satAdd 1 (satAdd s1 s2), st2)
      | .forallE _ ty body _ =>
        let st0 := pushTok st "FA"
        let ((_, s1), st1) := walkExpr ty st0
        let ((_, s2), st2) := walkExpr body st1
        (satAdd 1 (satAdd s1 s2), st2)
      | .letE _ ty val body _ =>
        let st0 := pushTok st "LT"
        let ((_, s1), st1) := walkExpr ty st0
        let ((_, s2), st2) := walkExpr val st1
        let ((_, s3), st3) := walkExpr body st2
        (satAdd 1 (satAdd s1 (satAdd s2 s3)), st3)
      | .lit _ =>
        let st0 := pushTok st "ST"
        (1, st0)
      | .mdata _ inner =>
        let ((_, s1), st1) := walkExpr inner st
        (s1, st1)
      | .proj _ idx struct =>
        let st0 := pushTok st s!"PR BV{idx}"
        let ((_, s1), st1) := walkExpr struct st0
        (satAdd 1 s1, st1)
    let nid := st1.nextId
    let st2 : WalkState := {
      st1 with
      nextId := nid + 1
      dagNodes := st1.dagNodes + 1
      memo := st1.memo.insert e (nid, tsz)
    }
    ((nid, tsz), st2)

def encodeStrArray (xs : Array String) : String :=
  let inner := xs.map fun s => "\"" ++ jsonEscape s ++ "\""
  "[" ++ String.intercalate ", " inner.toList ++ "]"

def splitColonPaths (s : String) : List System.FilePath :=
  (s.splitOn ":").filter (· != "") |>.map System.FilePath.mk

def runExport (modStr rootPrefix outPathStr : String) (extraPaths : List System.FilePath) : IO Unit := do
  let sysroot ← Lean.findSysroot
  let sp := if extraPaths.isEmpty then [System.FilePath.mk "build/lean"] else extraPaths
  Lean.initSearchPath sysroot sp
  let modName := String.toName modStr
  let env ← Lean.importModules #[{ module := modName }] {}

  let mut entries : Array (String × String × Nat × Nat × Nat × Nat × Array String × Array String × String) := #[]
  for (name, cinfo) in env.constants.map₁.toList do
    let s := name.toString
    if !matchesPrefix s rootPrefix || isInternalDecl s then
      continue
    let optKindTyVal : Option (String × Expr × Expr) :=
      match cinfo with
      | .thmInfo v => some ("thm", v.type, v.value)
      | .defnInfo v => some ("def", v.type, v.value)
      | _ => none
    match optKindTyVal with
    | none => continue
    | some (kind, tyExpr, valExpr) =>
      let headTok := if kind == "thm" then "THM" else "DEF"
      let initSt : WalkState := {
        rootPrefix := rootPrefix
        selfName := s
        tokens := #[headTok, s!"C_{s}", ":"]
      }
      let ((_, tyTree), stTy) := walkExpr tyExpr initSt
      let tyDag := stTy.dagNodes
      let stMid := pushTok stTy ":="
      let ((_, valTree), stFin) := walkExpr valExpr stMid
      let valDag := stFin.dagNodes - tyDag
      let depsArr := (stFin.deps.toList.mergeSort (· < ·)).toArray
      let axArr := (stFin.axioms.toList.mergeSort (· < ·)).toArray
      let tokStr := String.intercalate " " stFin.tokens.toList
      entries := entries.push (s, kind, tyTree, tyDag, valTree, valDag, depsArr, axArr, tokStr)

  let sorted := entries.qsort (fun a b => a.1 < b.1)
  let mut declJsons : Array String := #[]
  for (nm, kind, tyT, tyD, valT, valD, depsArr, axArr, tokStr) in sorted do
    let item :=
      "    {\n" ++
      s!"      \"name\": \"{jsonEscape nm}\",\n" ++
      s!"      \"kind\": \"{kind}\",\n" ++
      s!"      \"type_tree_nodes\": {tyT},\n" ++
      s!"      \"type_dag_nodes\": {tyD},\n" ++
      s!"      \"proof_tree_nodes\": {valT},\n" ++
      s!"      \"proof_dag_nodes\": {valD},\n" ++
      s!"      \"deps\": {encodeStrArray depsArr},\n" ++
      s!"      \"axioms\": {encodeStrArray axArr},\n" ++
      s!"      \"expr_tokens\": \"{jsonEscape tokStr}\"\n" ++
      "    }"
    declJsons := declJsons.push item

  let jsonOut :=
    "{\n" ++
    s!"  \"module\": \"{jsonEscape modStr}\",\n" ++
    s!"  \"prefix\": \"{jsonEscape rootPrefix}\",\n" ++
    s!"  \"decl_count\": {sorted.size},\n" ++
    "  \"decls\": [\n" ++
    String.intercalate ",\n" declJsons.toList ++
    "\n  ]\n}\n"
  IO.FS.writeFile (System.FilePath.mk outPathStr) jsonOut

end LeanExprExport

def main (args : List String) : IO UInt32 := do
  match args with
  | modStr :: rootPrefix :: outPathStr :: rest =>
    let paths := rest.foldl (fun acc arg => acc ++ LeanExprExport.splitColonPaths arg) []
    LeanExprExport.runExport modStr rootPrefix outPathStr paths
    return 0
  | _ =>
    IO.eprintln "Usage: lean --run lean_expr_export.lean <Module> <Prefix> <OutJson> [searchPaths...]"
    return 1
