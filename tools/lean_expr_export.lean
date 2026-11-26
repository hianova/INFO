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
    ".eq_", ".rec", ".casesOn", ".noConfusion", ".below", ".brecOn", ".sizeOf_spec",
    "._sizeOf_", ".ctorIdx", "._flat_ctor", ".injEq", ".inj"]
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
  projUses : Std.HashSet String := {}
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
      | .proj typeName idx struct =>
        let stP : WalkState := { st with projUses := st.projUses.insert s!"{typeName}#{idx}" }
        let st0 := pushTok stP s!"PR BV{idx}"
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

partial def collectUnusedHypsAux (pos : Nat) (ty val : Expr) (acc : Array String) : Array String :=
  match ty, val with
  | .forallE bn _ bodyTy _, .lam _ _ bodyVal _ =>
    let acc' :=
      if !bodyTy.hasLooseBVar 0 && !bodyVal.hasLooseBVar 0 then
        let s := bn.toString
        let label := if s.isEmpty || s == "[anonymous]" then s!"_arg{pos}" else s
        acc.push label
      else acc
    collectUnusedHypsAux (pos + 1) bodyTy bodyVal acc'
  | _, _ => acc

def collectUnusedHyps (ty val : Expr) : Array String :=
  collectUnusedHypsAux 0 ty val #[]

def runExport (modStr rootPrefix outPathStr : String) (extraPaths : List System.FilePath) : IO Unit := do
  let sysroot ← Lean.findSysroot
  let sp := if extraPaths.isEmpty then [System.FilePath.mk "build/lean"] else extraPaths
  Lean.initSearchPath sysroot sp
  let modName := String.toName modStr
  let env ← Lean.importModules #[{ module := modName }] {}

  let mut structEntries : Array (String × Array String) := #[]
  for (name, _) in env.constants.map₁.toList do
    let s := name.toString
    if matchesPrefix s rootPrefix && !isInternalDecl s then
      if let some sinfo := Lean.getStructureInfo? env name then
        structEntries := structEntries.push (s, sinfo.fieldNames.map Lean.Name.toString)
  let sortedStructs := structEntries.qsort (fun a b => a.1 < b.1)
  let mut structJsons : Array String := #[]
  for (snm, fields) in sortedStructs do
    structJsons := structJsons.push (
      "    {\"name\": \"" ++ jsonEscape snm ++ "\", \"fields\": " ++ encodeStrArray fields ++ "}"
    )

  let mut entries : Array (String × String × Nat × Nat × Nat × Nat × Array String × Array String × Array String × Array String × String) := #[]
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
      let projArr := (stFin.projUses.toList.mergeSort (· < ·)).toArray
      let unusedArr := if kind == "thm" then collectUnusedHyps tyExpr valExpr else #[]
      let tokStr := String.intercalate " " stFin.tokens.toList
      entries := entries.push (s, kind, tyTree, tyDag, valTree, valDag, depsArr, axArr, projArr, unusedArr, tokStr)

  let sorted := entries.qsort (fun a b => a.1 < b.1)
  let mut declJsons : Array String := #[]
  for (nm, kind, tyT, tyD, valT, valD, depsArr, axArr, projArr, unusedArr, tokStr) in sorted do
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
      s!"      \"proj_uses\": {encodeStrArray projArr},\n" ++
      s!"      \"unused_hyps\": {encodeStrArray unusedArr},\n" ++
      s!"      \"expr_tokens\": \"{jsonEscape tokStr}\"\n" ++
      "    }"
    declJsons := declJsons.push item

  let jsonOut :=
    "{\n" ++
    s!"  \"module\": \"{jsonEscape modStr}\",\n" ++
    s!"  \"prefix\": \"{jsonEscape rootPrefix}\",\n" ++
    s!"  \"decl_count\": {sorted.size},\n" ++
    "  \"structures\": [\n" ++
    String.intercalate ",\n" structJsons.toList ++
    "\n  ],\n" ++
    "  \"decls\": [\n" ++
    String.intercalate ",\n" declJsons.toList ++
    "\n  ]\n}\n"
  IO.FS.writeFile (System.FilePath.mk outPathStr) jsonOut

end LeanExprExport

namespace LeanDagExport

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _ =>
      let code := c.toNat
      if code < 32 then
        let hi := (code / 16) % 16
        let lo := code % 16
        acc ++ "\\u00" ++ String.singleton (hexDigit hi) ++ String.singleton (hexDigit lo)
      else
        acc.push c) ""

private def quoteJson (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def biToNat : Lean.BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

private def dataValToStr : Lean.DataValue → String
  | .ofString s => "S:" ++ s
  | .ofBool b => "B:" ++ toString b
  | .ofName n => "N:" ++ n.toString
  | .ofNat n => "U:" ++ toString n
  | .ofInt i => "I:" ++ toString i
  | .ofSyntax s => "X:" ++ toString s

private def mdataToStr (kv : Lean.MData) : String :=
  String.intercalate ";" (kv.entries.map (fun (k, v) => k.toString ++ "=" ++ dataValToStr v))

structure DagState where
  strMap : Std.HashMap String Nat := ∅
  strs : Array String := #[]
  constMap : Std.HashMap String Nat := ∅
  consts : Array String := #[]
  levelMap : Std.HashMap Lean.Level Nat := ∅
  levels : Array (Nat × Nat × Nat) := #[]
  lvlListMap : Std.HashMap (List Nat) Nat := ∅
  lvlLists : Array (Array Nat) := #[]
  exprMap : Std.HashMap Lean.Expr Nat := ∅
  nodes : Array (Nat × Nat × Nat × Nat) := #[]

private def internStr (s : String) : StateM DagState Nat := do
  let st ← get
  match st.strMap[s]? with
  | some idx => return idx
  | none =>
    let idx := st.strs.size
    set { st with strMap := st.strMap.insert s idx, strs := st.strs.push s }
    return idx

private def internConst (s : String) : StateM DagState Nat := do
  let st ← get
  match st.constMap[s]? with
  | some idx => return idx
  | none =>
    let idx := st.consts.size
    set { st with constMap := st.constMap.insert s idx, consts := st.consts.push s }
    return idx

private def internLevel (lvl : Lean.Level) : StateM DagState Nat := do
  let st ← get
  match st.levelMap[lvl]? with
  | some idx => return idx
  | none =>
    let row ← match lvl with
      | .zero => pure (0, 0, 0)
      | .succ u =>
        let ui ← internLevel u
        pure (1, ui, 0)
      | .max u v =>
        let ui ← internLevel u
        let vi ← internLevel v
        pure (2, ui, vi)
      | .imax u v =>
        let ui ← internLevel u
        let vi ← internLevel v
        pure (3, ui, vi)
      | .param n =>
        let ni ← internStr n.toString
        pure (4, ni, 0)
      | .mvar id =>
        let ni ← internStr id.name.toString
        pure (5, ni, 0)
    let st2 ← get
    let idx := st2.levels.size
    set { st2 with levelMap := st2.levelMap.insert lvl idx, levels := st2.levels.push row }
    return idx

private def internLevelList (lvls : List Lean.Level) : StateM DagState Nat := do
  let ids ← lvls.mapM internLevel
  let st ← get
  match st.lvlListMap[ids]? with
  | some idx => return idx
  | none =>
    let idx := st.lvlLists.size
    set { st with lvlListMap := st.lvlListMap.insert ids idx, lvlLists := st.lvlLists.push ids.toArray }
    return idx

private def pushNode (row : Nat × Nat × Nat × Nat) : StateM DagState Nat := do
  let st ← get
  let idx := st.nodes.size
  set { st with nodes := st.nodes.push row }
  return idx

private partial def internExpr (e : Lean.Expr) : StateM DagState Nat := do
  let st ← get
  match st.exprMap[e]? with
  | some idx => return idx
  | none =>
    let row ← match e with
      | .bvar idx => pure (0, idx, 0, 0)
      | .fvar id =>
        let si ← internStr id.name.toString
        pure (1, si, 0, 0)
      | .mvar id =>
        let si ← internStr id.name.toString
        pure (2, si, 0, 0)
      | .sort u =>
        let li ← internLevel u
        pure (3, li, 0, 0)
      | .const nm lvls =>
        let ci ← internConst nm.toString
        let lli ← internLevelList lvls
        pure (4, ci, lli, 0)
      | .app fn arg =>
        let fi ← internExpr fn
        let ai ← internExpr arg
        pure (5, fi, ai, 0)
      | .lam nm ty body bi =>
        let ti ← internExpr ty
        let biId ← internExpr body
        let si ← internStr nm.toString
        pure (6, ti, biId, si * 8 + biToNat bi)
      | .forallE nm ty body bi =>
        let ti ← internExpr ty
        let biId ← internExpr body
        let si ← internStr nm.toString
        pure (7, ti, biId, si * 8 + biToNat bi)
      | .letE nm ty val body nonDep =>
        let ti ← internExpr ty
        let vi ← internExpr val
        let helper ← pushNode (12, ti, vi, 0)
        let biId ← internExpr body
        let si ← internStr nm.toString
        let nd := if nonDep then 1 else 0
        pure (8, helper, biId, si * 2 + nd)
      | .lit l =>
        match l with
        | .natVal n =>
          let si ← internStr (toString n)
          pure (9, 0, si, 0)
        | .strVal s =>
          let si ← internStr s
          pure (9, 1, si, 0)
      | .mdata kv inner =>
        let ii ← internExpr inner
        let si ← internStr (mdataToStr kv)
        pure (10, ii, si, 0)
      | .proj typeName idx struct =>
        let si ← internExpr struct
        let ci ← internConst typeName.toString
        pure (11, si, ci, idx)
    let st2 ← get
    let nid := st2.nodes.size
    set { st2 with exprMap := st2.exprMap.insert e nid, nodes := st2.nodes.push row }
    return nid

private def constKindAndExprs : Lean.ConstantInfo → String × Lean.Expr × Option Lean.Expr
  | .thmInfo v => ("thm", v.type, some v.value)
  | .defnInfo v => ("def", v.type, some v.value)
  | .opaqueInfo v => ("opaque", v.type, some v.value)
  | .axiomInfo v => ("axiom", v.type, none)
  | .inductInfo v => ("induct", v.type, none)
  | .ctorInfo v => ("ctor", v.type, none)
  | .recInfo v => ("rec", v.type, none)
  | .quotInfo v => ("quot", v.type, none)

structure ExportedDecl where
  name : String
  kind : String
  lparams : Array Nat
  typeRoot : Nat
  valRoot : Option Nat
  deriving Inhabited

structure ExportedCtor where
  name : String
  typeRoot : Nat
  deriving Inhabited

structure ExportedInductType where
  name : String
  typeRoot : Nat
  ctors : Array ExportedCtor
  deriving Inhabited

structure ExportedInductGroup where
  lparams : Array Nat
  numParams : Nat
  isUnsafe : Bool
  types : Array ExportedInductType
  deriving Inhabited

structure ExportedDefMeta where
  declIdx : Nat
  safetyId : Nat
  hintKind : Nat
  hintHeight : Nat
  allNames : Array String
  deriving Inhabited

private partial def scanExprConstsAux (e : Lean.Expr) :
    StateM (Std.HashSet Lean.Expr × Array Lean.Name) Unit := do
  let (seen, _) ← get
  if seen.contains e then
    return ()
  modify fun (s, arr) => (s.insert e, arr)
  match e with
  | .const nm _ =>
    modify fun (s, arr) => (s, arr.push nm)
  | .app fn arg =>
    scanExprConstsAux fn
    scanExprConstsAux arg
  | .lam _ ty body _ | .forallE _ ty body _ =>
    scanExprConstsAux ty
    scanExprConstsAux body
  | .letE _ ty val body _ =>
    scanExprConstsAux ty
    scanExprConstsAux val
    scanExprConstsAux body
  | .mdata _ inner | .proj _ _ inner =>
    scanExprConstsAux inner
  | _ => pure ()

private def collectCInfoDeps (env : Lean.Environment) (cinfo : Lean.ConstantInfo) : Array Lean.Name :=
  let act : StateM (Std.HashSet Lean.Expr × Array Lean.Name) Unit := do
    scanExprConstsAux cinfo.type
    match cinfo with
    | .thmInfo v => scanExprConstsAux v.value
    | .defnInfo v =>
      scanExprConstsAux v.value
      for nm in v.all do
        modify fun (s, arr) => (s, arr.push nm)
    | .opaqueInfo v => scanExprConstsAux v.value
    | .inductInfo v =>
      for nm in v.all do
        modify fun (s, arr) => (s, arr.push nm)
      for ctor in v.ctors do
        modify fun (s, arr) => (s, arr.push ctor)
        if let some cc := env.find? ctor then
          scanExprConstsAux cc.type
    | .ctorInfo v =>
      modify fun (s, arr) => (s, arr.push v.induct)
      if let some ic := env.find? v.induct then
        scanExprConstsAux ic.type
    | .recInfo v =>
      for nm in v.all do
        modify fun (s, arr) => (s, arr.push nm)
    | _ => pure ()
  (act.run (∅, #[])).2.2

private def inTargetScope (env : Lean.Environment) (modStr rootPrefix : String) (nm : Lean.Name) : Bool :=
  match env.getModuleIdxFor? nm with
  | some midx =>
    let mname := (env.header.moduleNames[midx.toNat]!).toString
    mname.startsWith rootPrefix || mname == modStr
  | none =>
    nm.toString.startsWith rootPrefix

private def safetyToNat : Lean.DefinitionSafety → Nat
  | .safe => 0
  | .unsafe => 1
  | .partial => 2

private def hintsToPair : Lean.ReducibilityHints → Nat × Nat
  | .opaque => (0, 0)
  | .abbrev => (1, 0)
  | .regular h => (2, h.toNat)

def runExportDag (modStr rootPrefix outPathStr : String) (extraPaths : List System.FilePath)
    (withInternalDeps : Bool := false) : IO Unit := do
  let sysroot ← Lean.findSysroot
  let allPaths := extraPaths ++ [System.FilePath.mk "build/lean"]
  Lean.initSearchPath sysroot allPaths
  let modName := modStr.toName
  let env ← Lean.importModules #[{ module := modName }] {}
  let matchesRaw ← if !withInternalDeps then
    pure (env.constants.map₁.toList.filter fun (nm, _) =>
      nm.toString.startsWith rootPrefix && !nm.isInternal)
  else do
    let mut worklist : Array Lean.Name := #[]
    let mut visited : Std.HashSet Lean.Name := ∅
    let mut collected : List (Lean.Name × Lean.ConstantInfo) := []
    for (nm, _) in env.constants.map₁.toList do
      if nm.toString.startsWith rootPrefix && !nm.isInternal then
        if !visited.contains nm then
          visited := visited.insert nm
          worklist := worklist.push nm
    let mut head := 0
    while head < worklist.size do
      let cur := worklist[head]!
      head := head + 1
      if let some cinfo := env.find? cur then
        collected := (cur, cinfo) :: collected
        let deps := collectCInfoDeps env cinfo
        for dep in deps do
          if !visited.contains dep && inTargetScope env modStr rootPrefix dep then
            if (env.find? dep).isSome then
              visited := visited.insert dep
              worklist := worklist.push dep
    pure collected
  let sorted := matchesRaw.toArray.qsort fun a b => a.1.toString < b.1.toString
  let action : StateM DagState (Array ExportedDecl × Array ExportedInductGroup × Array ExportedDefMeta) := do
    let mut out : Array ExportedDecl := #[]
    let mut indGroups : Array ExportedInductGroup := #[]
    let mut seenIndRoots : Std.HashSet Lean.Name := ∅
    let mut defMetas : Array ExportedDefMeta := #[]
    for (nm, cinfo) in sorted do
      let (kind, ty, valOpt) := constKindAndExprs cinfo
      let lparams ← (cinfo.levelParams.mapM (fun lp => internStr lp.toString))
      let tyId ← internExpr ty
      let valId ← match valOpt with
        | some v =>
          let vid ← internExpr v
          pure (some vid)
        | none => pure none
      let dIdx := out.size
      out := out.push {
        name := nm.toString
        kind := kind
        lparams := lparams.toArray
        typeRoot := tyId
        valRoot := valId
      }
      if withInternalDeps then
        match cinfo with
        | .inductInfo iv =>
          let rootNm := iv.all.headD nm
          if !seenIndRoots.contains rootNm then
            seenIndRoots := seenIndRoots.insert rootNm
            let grpLp ← (iv.levelParams.mapM (fun lp => internStr lp.toString))
            let mut indTypes : Array ExportedInductType := #[]
            for indNm in iv.all do
              if let some (.inductInfo ivSub) := env.find? indNm then
                let indTyId ← internExpr ivSub.type
                let mut ctorsArr : Array ExportedCtor := #[]
                for ctorNm in ivSub.ctors do
                  if let some cc := env.find? ctorNm then
                    let cTyId ← internExpr cc.type
                    ctorsArr := ctorsArr.push { name := ctorNm.toString, typeRoot := cTyId }
                indTypes := indTypes.push { name := indNm.toString, typeRoot := indTyId, ctors := ctorsArr }
            indGroups := indGroups.push {
              lparams := grpLp.toArray
              numParams := iv.numParams
              isUnsafe := iv.isUnsafe
              types := indTypes
            }
        | .defnInfo dv =>
          let (hk, hh) := hintsToPair dv.hints
          defMetas := defMetas.push {
            declIdx := dIdx
            safetyId := safetyToNat dv.safety
            hintKind := hk
            hintHeight := hh
            allNames := (dv.all.map Lean.Name.toString).toArray
          }
        | _ => pure ()
    return (out, indGroups, defMetas)
  let ((decls, indGroups, defMetas), st) := action.run {}
  let mut treeSizes : Array Nat := Array.mkEmpty st.nodes.size
  let mut treeNodesTotal : Nat := 0
  for (tag, a, b, _) in st.nodes do
    let sz := match tag with
      | 5 | 6 | 7 => 1 + treeSizes[a]! + treeSizes[b]!
      | 8 => 1 + treeSizes[a]! + treeSizes[b]!
      | 12 => treeSizes[a]! + treeSizes[b]!
      | 10 | 11 => 1 + treeSizes[a]!
      | _ => 1
    treeSizes := treeSizes.push sz
  for d in decls do
    treeNodesTotal := treeNodesTotal + treeSizes[d.typeRoot]!
    match d.valRoot with
    | some vr => treeNodesTotal := treeNodesTotal + treeSizes[vr]!
    | none => pure ()
  IO.FS.withFile (System.FilePath.mk outPathStr) .write fun h => do
    h.putStr "{"
    h.putStr "\"format\":\"lean-proof-dag-v1\","
    h.putStr ("\"module\":" ++ quoteJson modStr ++ ",")
    h.putStr ("\"prefix\":" ++ quoteJson rootPrefix ++ ",")
    h.putStr ("\"stats\":{\"decl_count\":" ++ toString decls.size
      ++ ",\"global_dag_nodes\":" ++ toString st.nodes.size
      ++ ",\"total_tree_nodes\":" ++ toString treeNodesTotal ++ "},")
    h.putStr "\"str_pool\":["
    for i in [:st.strs.size] do
      if i > 0 then h.putStr ","
      h.putStr (quoteJson st.strs[i]!)
    h.putStr "],\"consts\":["
    for i in [:st.consts.size] do
      if i > 0 then h.putStr ","
      h.putStr (quoteJson st.consts[i]!)
    h.putStr "],\"levels\":["
    for i in [:st.levels.size] do
      if i > 0 then h.putStr ","
      let (t, a, b) := st.levels[i]!
      h.putStr ("[" ++ toString t ++ "," ++ toString a ++ "," ++ toString b ++ "]")
    h.putStr "],\"level_lists\":["
    for i in [:st.lvlLists.size] do
      if i > 0 then h.putStr ","
      let xs := st.lvlLists[i]!
      h.putStr "["
      for j in [:xs.size] do
        if j > 0 then h.putStr ","
        h.putStr (toString xs[j]!)
      h.putStr "]"
    h.putStr "],\"nodes\":["
    for i in [:st.nodes.size] do
      if i > 0 then h.putStr ","
      let (t, a, b, c) := st.nodes[i]!
      h.putStr ("[" ++ toString t ++ "," ++ toString a ++ "," ++ toString b ++ "," ++ toString c ++ "]")
    h.putStr "],\"decls\":["
    for i in [:decls.size] do
      if i > 0 then h.putStr ","
      let d := decls[i]!
      h.putStr ("{\"name\":" ++ quoteJson d.name
        ++ ",\"kind\":" ++ quoteJson d.kind
        ++ ",\"lparams\":[")
      for j in [:d.lparams.size] do
        if j > 0 then h.putStr ","
        h.putStr (toString d.lparams[j]!)
      let valStr := match d.valRoot with | some v => toString v | none => "null"
      h.putStr ("],\"type\":" ++ toString d.typeRoot ++ ",\"val\":" ++ valStr ++ "}")
    if withInternalDeps then
      h.putStr "],\"induct_groups\":["
      for i in [:indGroups.size] do
        if i > 0 then h.putStr ","
        let g := indGroups[i]!
        h.putStr "{\"lparams\":["
        for j in [:g.lparams.size] do
          if j > 0 then h.putStr ","
          h.putStr (toString g.lparams[j]!)
        h.putStr ("],\"nparams\":" ++ toString g.numParams ++ ",\"is_unsafe\":" ++ (if g.isUnsafe then "true" else "false") ++ ",\"types\":[")
        for ti in [:g.types.size] do
          if ti > 0 then h.putStr ","
          let tp := g.types[ti]!
          h.putStr ("{\"name\":" ++ quoteJson tp.name ++ ",\"type\":" ++ toString tp.typeRoot ++ ",\"ctors\":[")
          for ci in [:tp.ctors.size] do
            if ci > 0 then h.putStr ","
            let ct := tp.ctors[ci]!
            h.putStr ("[" ++ quoteJson ct.name ++ "," ++ toString ct.typeRoot ++ "]")
          h.putStr "]}"
        h.putStr "]}"
      h.putStr "],\"def_meta\":["
      for i in [:defMetas.size] do
        if i > 0 then h.putStr ","
        let dm := defMetas[i]!
        h.putStr ("[" ++ toString dm.declIdx ++ "," ++ toString dm.safetyId ++ "," ++ toString dm.hintKind ++ "," ++ toString dm.hintHeight ++ ",[")
        for j in [:dm.allNames.size] do
          if j > 0 then h.putStr ","
          h.putStr (quoteJson dm.allNames[j]!)
        h.putStr "]]"
    h.putStr "]}\n"

private def strToName (s : String) : Lean.Name :=
  if s.isEmpty || s == "[anonymous]" then .anonymous else s.toName

private def natToBI (n : Nat) : Lean.BinderInfo :=
  match n with
  | 1 => .implicit
  | 2 => .strictImplicit
  | 3 => .instImplicit
  | _ => .default

private def unwrapExcept {α : Type} (msg : String) : Except String α → IO α
  | .ok v => return v
  | .error e => throw (IO.userError s!"{msg}: {e}")

private def jsonArrNat (j : Lean.Json) (msg : String) : IO (Array Nat) := do
  let arr ← unwrapExcept msg j.getArr?
  arr.mapM fun el => unwrapExcept msg el.getNat?

private structure ParsedDecl where
  name : String
  kind : String
  lparams : List Lean.Name
  typeId : Nat
  valId : Option Nat
  deriving Inhabited

private structure ReplayUnit where
  primaryName : Lean.Name
  ownedNames : Array Lean.Name
  roots : Array Lean.Expr
  decl : Lean.Declaration

private instance : Inhabited ReplayUnit :=
  ⟨{ primaryName := .anonymous
     ownedNames := #[]
     roots := #[]
     decl := .axiomDecl { name := .anonymous, levelParams := [], type := .sort .zero, isUnsafe := false } }⟩

private def jsonObjArr (j : Lean.Json) (key : String) : IO (Array Lean.Json) := do
  let v ← unwrapExcept s!"missing {key}" (j.getObjVal? key)
  unwrapExcept s!"expected array at {key}" v.getArr?

private def jsonObjStrArr (j : Lean.Json) (key : String) : IO (Array String) := do
  let arr ← jsonObjArr j key
  arr.mapM fun el => unwrapExcept s!"expected str in {key}" el.getStr?

private def jsonObjStr (j : Lean.Json) (key : String) : IO String := do
  let v ← unwrapExcept s!"missing {key}" (j.getObjVal? key)
  unwrapExcept s!"expected str at {key}" v.getStr?

private def jsonObjNat (j : Lean.Json) (key : String) : IO Nat := do
  let v ← unwrapExcept s!"missing {key}" (j.getObjVal? key)
  unwrapExcept s!"expected nat at {key}" v.getNat?

def replayDagToKernelEnv (dagJsonPath : String) (baseModules : List String)
    (extraPaths : List System.FilePath) : IO (Lean.Kernel.Environment × Nat × Nat × Nat) := do
  let sysroot ← Lean.findSysroot
  Lean.initSearchPath sysroot extraPaths
  let baseMods := if baseModules.isEmpty then ["Init"] else baseModules
  let imports := baseMods.toArray.map fun m => { module := m.toName : Lean.Import }
  let env ← Lean.importModules imports {}

  let raw ← IO.FS.readFile (System.FilePath.mk dagJsonPath)
  let rootJson ← unwrapExcept "JSON parse failed" (Lean.Json.parse raw)
  let strs ← jsonObjStrArr rootJson "str_pool"
  let consts ← jsonObjStrArr rootJson "consts"

  for cs in consts do
    if cs == "sorryAx" || cs == "Lean.ofReduceBool" then
      throw (IO.userError s!"Illegal axiom detected in Proof-DAG: {cs}")

  let lvlJsonArr ← jsonObjArr rootJson "levels"
  let mut levels : Array Lean.Level := Array.mkEmpty lvlJsonArr.size
  for lj in lvlJsonArr do
    let row ← jsonArrNat lj "level row"
    let t := row[0]!
    let a := row[1]!
    let b := row[2]!
    let lv : Lean.Level := match t with
      | 0 => .zero
      | 1 => .succ levels[a]!
      | 2 => .max levels[a]! levels[b]!
      | 3 => .imax levels[a]! levels[b]!
      | 4 => .param (strToName strs[a]!)
      | _ => .mvar { name := strToName strs[a]! }
    levels := levels.push lv

  let llJsonArr ← jsonObjArr rootJson "level_lists"
  let mut lvlLists : Array (List Lean.Level) := Array.mkEmpty llJsonArr.size
  for llj in llJsonArr do
    let row ← jsonArrNat llj "lvl list row"
    lvlLists := lvlLists.push (row.toList.map fun id => levels[id]!)

  let nodesJsonArr ← jsonObjArr rootJson "nodes"
  let mut exprs : Array Lean.Expr := Array.mkEmpty nodesJsonArr.size
  let mut letBinds : Std.HashMap Nat (Lean.Expr × Lean.Expr) := ∅
  for nid in [:nodesJsonArr.size] do
    let row ← jsonArrNat nodesJsonArr[nid]! "node row"
    let tag := row[0]!
    let a := row[1]!
    let b := row[2]!
    let cc := row[3]!
    let ex : Lean.Expr ← match tag with
      | 0 => pure (.bvar a)
      | 1 => pure (.fvar { name := strToName strs[a]! })
      | 2 => pure (.mvar { name := strToName strs[a]! })
      | 3 => pure (.sort levels[a]!)
      | 4 => pure (.const (strToName consts[a]!) lvlLists[b]!)
      | 5 => pure (.app exprs[a]! exprs[b]!)
      | 6 => pure (.lam (strToName strs[cc / 8]!) exprs[a]! exprs[b]! (natToBI (cc % 8)))
      | 7 => pure (.forallE (strToName strs[cc / 8]!) exprs[a]! exprs[b]! (natToBI (cc % 8)))
      | 8 =>
        match letBinds[a]? with
        | some (lty, lval) =>
          pure (.letE (strToName strs[cc / 2]!) lty lval exprs[b]! (cc % 2 == 1))
        | none =>
          throw (IO.userError s!"Missing letBind node {a} for letE at {nid}")
      | 9 =>
        let s := strs[b]!
        if a == 0 then
          match s.toNat? with
          | some nv => pure (.lit (.natVal nv))
          | none => throw (IO.userError s!"Invalid nat literal: {s}")
        else
          pure (.lit (.strVal s))
      | 10 => pure (.mdata .empty exprs[a]!)
      | 11 => pure (.proj (strToName consts[b]!) cc exprs[a]!)
      | 12 =>
        letBinds := letBinds.insert nid (exprs[a]!, exprs[b]!)
        pure exprs[a]!
      | _ => throw (IO.userError s!"Unknown node tag {tag} at {nid}")
    exprs := exprs.push ex

  let declsJsonArr ← jsonObjArr rootJson "decls"
  let mut parsedDecls : Array ParsedDecl := Array.mkEmpty declsJsonArr.size
  for dj in declsJsonArr do
    let nm ← jsonObjStr dj "name"
    let kd ← jsonObjStr dj "kind"
    let lpsNat ← jsonArrNat (← unwrapExcept "decl.lparams" (dj.getObjVal? "lparams")) "decl.lparams"
    let tyId ← jsonObjNat dj "type"
    let valJson ← unwrapExcept "decl.val" (dj.getObjVal? "val")
    let valId := match valJson with
      | .null => none
      | _ => valJson.getNat?.toOption
    parsedDecls := parsedDecls.push {
      name := nm
      kind := kd
      lparams := lpsNat.toList.map fun id => strToName strs[id]!
      typeId := tyId
      valId := valId
    }

  let mut defMetaMap : Std.HashMap Nat (Lean.DefinitionSafety × Lean.ReducibilityHints × Array String) := ∅
  if let .ok dmJson := rootJson.getObjVal? "def_meta" then
    let dmArr ← unwrapExcept "def_meta arr" dmJson.getArr?
    for rowj in dmArr do
      let arr ← unwrapExcept "def_meta row" rowj.getArr?
      let dIdx ← unwrapExcept "def_meta idx" arr[0]!.getNat?
      let sId ← unwrapExcept "def_meta safety" arr[1]!.getNat?
      let hk ← unwrapExcept "def_meta hk" arr[2]!.getNat?
      let hh ← unwrapExcept "def_meta hh" arr[3]!.getNat?
      let allJson ← unwrapExcept "def_meta all" arr[4]!.getArr?
      let allStrs ← allJson.mapM fun el => unwrapExcept "def_meta nm" el.getStr?
      let saf : Lean.DefinitionSafety := match sId with | 1 => .unsafe | 2 => .partial | _ => .safe
      let hint : Lean.ReducibilityHints := match hk with | 0 => .opaque | 1 => .abbrev | _ => .regular (UInt32.ofNat hh)
      defMetaMap := defMetaMap.insert dIdx (saf, hint, allStrs)

  let mut units : Array ReplayUnit := #[]
  let mut indOwnedNames : Std.HashSet Lean.Name := ∅
  if let .ok igJson := rootJson.getObjVal? "induct_groups" then
    let igArr ← unwrapExcept "induct_groups arr" igJson.getArr?
    for gj in igArr do
      let lpsNat ← jsonArrNat (← unwrapExcept "ig.lparams" (gj.getObjVal? "lparams")) "ig.lparams"
      let nparams ← unwrapExcept "ig.nparams" ((← unwrapExcept "ig.nparams" (gj.getObjVal? "nparams")).getNat?)
      let isUnsafe ← unwrapExcept "ig.is_unsafe" ((← unwrapExcept "ig.is_unsafe" (gj.getObjVal? "is_unsafe")).getBool?)
      let typesJson ← unwrapExcept "ig.types" ((← unwrapExcept "ig.types" (gj.getObjVal? "types")).getArr?)
      let mut indTypes : List Lean.InductiveType := []
      let mut owned : Array Lean.Name := #[]
      let mut roots : Array Lean.Expr := #[]
      for tj in typesJson do
        let tNameStr ← unwrapExcept "it.name" ((← unwrapExcept "it.name" (tj.getObjVal? "name")).getStr?)
        let tTyId ← unwrapExcept "it.type" ((← unwrapExcept "it.type" (tj.getObjVal? "type")).getNat?)
        let ctorsJson ← unwrapExcept "it.ctors" ((← unwrapExcept "it.ctors" (tj.getObjVal? "ctors")).getArr?)
        let tNm := strToName tNameStr
        let tTy := exprs[tTyId]!
        owned := owned.push tNm
        owned := owned.push (Lean.Name.mkStr tNm "rec")
        roots := roots.push tTy
        let mut ctorList : List Lean.Constructor := []
        for cj in ctorsJson do
          let cArr ← unwrapExcept "ctor row" cj.getArr?
          let cNameStr ← unwrapExcept "ctor.name" cArr[0]!.getStr?
          let cTyId ← unwrapExcept "ctor.type" cArr[1]!.getNat?
          let cNm := strToName cNameStr
          let cTy := exprs[cTyId]!
          owned := owned.push cNm
          roots := roots.push cTy
          ctorList := ctorList ++ [{ name := cNm, type := cTy }]
        indTypes := indTypes ++ [{ name := tNm, type := tTy, ctors := ctorList }]
      for nm in owned do
        indOwnedNames := indOwnedNames.insert nm
      let lps := lpsNat.toList.map fun id => strToName strs[id]!
      if !indTypes.isEmpty then
        units := units.push {
          primaryName := indTypes.head!.name
          ownedNames := owned
          roots := roots
          decl := .inductDecl lps nparams indTypes isUnsafe
        }

  -- Map decl name -> index for mutual def lookup
  let mut declByName : Std.HashMap String (Nat × ParsedDecl) := ∅
  for i in [:parsedDecls.size] do
    declByName := declByName.insert parsedDecls[i]!.name (i, parsedDecls[i]!)

  let mut handledDefs : Std.HashSet String := ∅
  for i in [:parsedDecls.size] do
    let d := parsedDecls[i]!
    let nm := strToName d.name
    if d.kind == "induct" || d.kind == "ctor" || d.kind == "rec" || d.kind == "quot" then
      if d.kind == "induct" && !indOwnedNames.contains nm then
        throw (IO.userError s!"Inductive {d.name} missing induct_groups metadata; re-export with --with-internal-deps")
      continue
    else if d.kind == "def" then
      if handledDefs.contains d.name then
        continue
      let (saf, hint, allStrs) := defMetaMap[i]?.getD (.safe, .regular 0, #[d.name])
      let mut allNames : List Lean.Name := []
      let mut dvals : List Lean.DefinitionVal := []
      let mut owned : Array Lean.Name := #[]
      let mut roots : Array Lean.Expr := #[]
      for an in allStrs do
        allNames := allNames ++ [strToName an]
      for an in allStrs do
        handledDefs := handledDefs.insert an
        if let some (idxAn, dAn) := declByName[an]? then
          let (sAn, hAn, _) := defMetaMap[idxAn]?.getD (saf, hint, allStrs)
          let tyE := exprs[dAn.typeId]!
          let valE := match dAn.valId with | some vid => exprs[vid]! | none => tyE
          let nmAn := strToName an
          owned := owned.push nmAn
          roots := roots.push tyE |>.push valE
          dvals := dvals ++ [{
            name := nmAn
            levelParams := dAn.lparams
            type := tyE
            value := valE
            hints := hAn
            safety := sAn
            all := allNames
          }]
      if dvals.length == 1 then
        units := units.push {
          primaryName := dvals.head!.name
          ownedNames := owned
          roots := roots
          decl := .defnDecl dvals.head!
        }
      else if dvals.length > 1 then
        units := units.push {
          primaryName := dvals.head!.name
          ownedNames := owned
          roots := roots
          decl := .mutualDefnDecl dvals
        }
    else if d.kind == "thm" then
      let tyE := exprs[d.typeId]!
      let valE := match d.valId with | some vid => exprs[vid]! | none => tyE
      units := units.push {
        primaryName := nm
        ownedNames := #[nm]
        roots := #[tyE, valE]
        decl := .thmDecl {
          name := nm
          levelParams := d.lparams
          type := tyE
          value := valE
        }
      }
    else if d.kind == "opaque" then
      let tyE := exprs[d.typeId]!
      let valE := match d.valId with | some vid => exprs[vid]! | none => tyE
      units := units.push {
        primaryName := nm
        ownedNames := #[nm]
        roots := #[tyE, valE]
        decl := .opaqueDecl {
          name := nm
          levelParams := d.lparams
          type := tyE
          value := valE
          isUnsafe := false
        }
      }
    else if d.kind == "axiom" then
      let tyE := exprs[d.typeId]!
      units := units.push {
        primaryName := nm
        ownedNames := #[nm]
        roots := #[tyE]
        decl := .axiomDecl {
          name := nm
          levelParams := d.lparams
          type := tyE
          isUnsafe := false
        }
      }

  -- Topological ordering (Kahn's algorithm) over ReplayUnits
  let mut ownerUnit : Std.HashMap Lean.Name Nat := ∅
  for ui in [:units.size] do
    for onm in units[ui]!.ownedNames do
      ownerUnit := ownerUnit.insert onm ui

  let mut indeg : Array Nat := Array.replicate units.size 0
  let mut adj : Array (Array Nat) := Array.replicate units.size #[]
  for ui in [:units.size] do
    let act : StateM (Std.HashSet Lean.Expr × Array Lean.Name) Unit := do
      for r in units[ui]!.roots do
        scanExprConstsAux r
    let deps := (act.run (∅, #[])).2.2
    let mut seenU : Std.HashSet Nat := ∅
    for depNm in deps do
      if let some depU := ownerUnit[depNm]? then
        if depU != ui && !seenU.contains depU then
          seenU := seenU.insert depU
          adj := adj.set! depU (adj[depU]!.push ui)
          indeg := indeg.set! ui (indeg[ui]! + 1)

  let mut queue : Array Nat := #[]
  for ui in [:units.size] do
    if indeg[ui]! == 0 then
      queue := queue.push ui
  let mut order : Array Nat := #[]
  let mut qh := 0
  while qh < queue.size do
    let u := queue[qh]!
    qh := qh + 1
    order := order.push u
    for v in adj[u]! do
      let nd := indeg[v]! - 1
      indeg := indeg.set! v nd
      if nd == 0 then
        queue := queue.push v

  if order.size != units.size then
    throw (IO.userError s!"Cycle or unresolved internal dep in DAG units: sorted {order.size}/{units.size}")

  let mut kenv := env.toKernelEnv
  let mut nInd := 0
  let mut nDef := 0
  let mut nThm := 0
  for ui in order do
    let u := units[ui]!
    if (kenv.find? u.primaryName).isSome then
      continue
    match kenv.addDecl Lean.Options.empty u.decl with
    | .ok kenv2 =>
      kenv := kenv2
      match u.decl with
      | .inductDecl .. => nInd := nInd + 1
      | .defnDecl .. | .mutualDefnDecl .. => nDef := nDef + 1
      | .thmDecl .. => nThm := nThm + 1
      | _ => pure ()
    | .error ex =>
      let msg ← (ex.toMessageData Lean.Options.empty).toString
      throw (IO.userError s!"Kernel rejected declaration {u.primaryName}: {msg}")

  return (kenv, nInd, nDef, nThm)

def runVerifyDag (dagJsonPath : String) (baseModules : List String)
    (extraPaths : List System.FilePath) : IO Unit := do
  let (_, nInd, nDef, nThm) ← replayDagToKernelEnv dagJsonPath baseModules extraPaths
  IO.println s!"[verify-dag] KERNEL PASS: inducts={nInd} defs={nDef} thms={nThm} (0 sorryAx, 0 ofReduceBool)"

private def collectTransitiveAxioms (kenv : Lean.Kernel.Environment)
    (roots : Array Lean.Name) : Array String := Id.run do
  let mut visited : Std.HashSet Lean.Name := ∅
  let mut worklist : Array Lean.Name := #[]
  let mut axioms : Std.HashSet String := ∅
  for r in roots do
    if !visited.contains r then
      visited := visited.insert r
      worklist := worklist.push r
  let mut qh := 0
  while qh < worklist.size do
    let nm := worklist[qh]!
    qh := qh + 1
    if let some cinfo := kenv.find? nm then
      match cinfo with
      | .axiomInfo _ =>
        axioms := axioms.insert nm.toString
      | _ =>
        let act : StateM (Std.HashSet Lean.Expr × Array Lean.Name) Unit := do
          scanExprConstsAux cinfo.type
          match cinfo with
          | .thmInfo v => scanExprConstsAux v.value
          | .defnInfo v => scanExprConstsAux v.value
          | .opaqueInfo v => scanExprConstsAux v.value
          | _ => pure ()
        let deps := (act.run (∅, #[])).2.2
        for dep in deps do
          if !visited.contains dep then
            visited := visited.insert dep
            worklist := worklist.push dep
  return (axioms.toList.mergeSort (· < ·)).toArray

private def jsonObjStrArrOpt (j : Lean.Json) (key : String) : IO (Option (Array String)) := do
  match j.getObjVal? key with
  | .error _ => return none
  | .ok .null => return none
  | .ok v =>
    let arr ← unwrapExcept s!"expected array at {key}" v.getArr?
    let xs ← arr.mapM fun el => unwrapExcept s!"expected str in {key}" el.getStr?
    return some xs

private def jsonObjStrOpt (j : Lean.Json) (key : String) : IO (Option String) := do
  match j.getObjVal? key with
  | .error _ => return none
  | .ok .null => return none
  | .ok v =>
    let s ← unwrapExcept s!"expected str at {key}" v.getStr?
    return if s.isEmpty then none else some s

def runVerifyContract (dagJsonPath contractJsonPath : String) (baseModules : List String)
    (extraPaths : List System.FilePath) : IO Unit := do
  let (kenv, nInd, nDef, nThm) ← replayDagToKernelEnv dagJsonPath baseModules extraPaths
  let cRaw ← IO.FS.readFile (System.FilePath.mk contractJsonPath)
  let cJson ← unwrapExcept "Contract JSON parse failed" (Lean.Json.parse cRaw)
  let thmNames ← jsonObjStrArr cJson "theorem_names"
  if thmNames.isEmpty then
    throw (IO.userError "Contract theorem_names must be non-empty")
  let permitted := (← jsonObjStrArrOpt cJson "permitted_axioms").getD #["propext", "Quot.sound", "Classical.choice"]
  let chalModOpt ← jsonObjStrOpt cJson "challenge_module"
  let forbiddenImports := (← jsonObjStrArrOpt cJson "forbidden_imports").getD #[]

  let mut chalEnvOpt : Option Lean.Environment := none
  if let some chalMod := chalModOpt then
    let chalEnv ← Lean.importModules #[{ module := chalMod.toName : Lean.Import }] {}
    for imp in chalEnv.header.imports do
      let impStr := imp.module.toString
      for forb in forbiddenImports do
        if impStr == forb || impStr.startsWith (forb ++ ".") || impStr.endsWith ("." ++ forb) then
          throw (IO.userError s!"TCB isolation violation: challenge module imports forbidden '{impStr}'")
    chalEnvOpt := some chalEnv

  let mut roots : Array Lean.Name := #[]
  for thmStr in thmNames do
    let thmNm := strToName thmStr
    roots := roots.push thmNm
    match kenv.find? thmNm with
    | some (.thmInfo solVal) =>
      if let some chalEnv := chalEnvOpt then
        match chalEnv.find? thmNm with
        | some chalInfo =>
          if solVal.levelParams != chalInfo.levelParams then
            throw (IO.userError s!"Contract levelParams mismatch for {thmStr}")
          if !Lean.Expr.eqv solVal.type chalInfo.type then
            throw (IO.userError s!"Contract type mismatch for {thmStr}")
        | none =>
          throw (IO.userError s!"Challenge module missing theorem {thmStr}")
    | _ =>
      throw (IO.userError s!"Replayed kernel environment missing theorem {thmStr}")

  let axiomsUsed := collectTransitiveAxioms kenv roots
  for ax in axiomsUsed do
    if !permitted.contains ax then
      throw (IO.userError s!"Disallowed axiom in contract closure: {ax}")

  let chalLabel := chalModOpt.getD "(none)"
  let axList := String.intercalate "," axiomsUsed.toList
  IO.println s!"[verify-contract] CONTRACT PASS: thms={thmNames.size} challenge={chalLabel} axioms=[{axList}] (replayed inducts={nInd} defs={nDef} thms={nThm})"

end LeanDagExport

def main (args : List String) : IO UInt32 := do
  match args with
  | "export-dag" :: "--with-internal-deps" :: modStr :: rootPrefix :: outPathStr :: rest =>
    let paths := rest.foldl (fun acc arg => acc ++ LeanExprExport.splitColonPaths arg) []
    LeanDagExport.runExportDag modStr rootPrefix outPathStr paths true
    return 0
  | "export-dag" :: modStr :: rootPrefix :: outPathStr :: rest =>
    let paths := rest.foldl (fun acc arg => acc ++ LeanExprExport.splitColonPaths arg) []
    LeanDagExport.runExportDag modStr rootPrefix outPathStr paths false
    return 0
  | "verify-dag" :: dagJsonPath :: rest =>
    let (baseMods, searchRest) := match rest with
      | b :: sr => (b.splitOn ",", sr)
      | [] => (["Init"], [])
    let paths := searchRest.foldl (fun acc arg => acc ++ LeanExprExport.splitColonPaths arg) []
    LeanDagExport.runVerifyDag dagJsonPath baseMods paths
    return 0
  | "verify-contract" :: dagJsonPath :: contractJsonPath :: rest =>
    let (baseMods, searchRest) := match rest with
      | b :: sr => (b.splitOn ",", sr)
      | [] => (["Init"], [])
    let paths := searchRest.foldl (fun acc arg => acc ++ LeanExprExport.splitColonPaths arg) []
    LeanDagExport.runVerifyContract dagJsonPath contractJsonPath baseMods paths
    return 0
  | modStr :: rootPrefix :: outPathStr :: rest =>
    let paths := rest.foldl (fun acc arg => acc ++ LeanExprExport.splitColonPaths arg) []
    LeanExprExport.runExport modStr rootPrefix outPathStr paths
    return 0
  | _ =>
    IO.eprintln "Usage: lean --run lean_expr_export.lean [export-dag [--with-internal-deps] | verify-dag | verify-contract] ..."
    return 1
