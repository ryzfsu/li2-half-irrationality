import Li2Lean
import Solution

open Lean Elab Command

namespace Li2Lean.ReleaseVerification

def body? (info : ConstantInfo) : Option Expr := info.value? true

def projectName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Li2Lean." || s.startsWith "Li2Bridges"

def inductiveLinks (env : Environment) (n : Name) : List Name :=
  if !projectName n then []
  else
    match env.find? n with
    | some (.inductInfo v) => v.all ++ v.ctors
    | some (.ctorInfo v) => [v.induct]
    | some (.recInfo v) =>
        v.all ++ v.rules.flatMap (fun r => r.ctor :: r.rhs.getUsedConstants.toList)
    | _ => []

def infoDeps (env : Environment) (info : ConstantInfo) : List Name :=
  let direct := info.type.getUsedConstants.toList ++
    ((body? info).map (fun e => e.getUsedConstants.toList) |>.getD [])
  direct ++ direct.flatMap (inductiveLinks env)

partial def closure (env : Environment) (todo : List Name)
    (seen : Std.HashSet Name) : Std.HashSet Name :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closure env rest seen
      | some info =>
        let next := infoDeps env info
        closure env (next ++ rest) seen

def hasPrefix (p : String) (n : Name) : Bool :=
  (n.toString == p) || (n.toString.startsWith (p ++ "."))

def forbiddenLines : List Name → List String
  | [] => []
  | n :: ns =>
    let tail := forbiddenLines ns
    if hasPrefix "Li2Lean.P0.Config.CAReceipt" n ||
       hasPrefix "Li2Lean.P0.CAReceiptSlack" n ||
       hasPrefix "Li2Lean.P0DualCertificate" n ||
       hasPrefix "Li2Lean.Li2Bridges" n ||
       hasPrefix "Li2Bridges" n ||
       hasPrefix "Li2Lean.P0.P0CoefficientStep" n ||
       n.toString.contains "CoefficientBridge" ||
       n.toString.contains "hS4" then
      s!"FORBIDDEN_REACHABLE {n}" :: tail
    else tail

def reportWithEnv (env : Environment) (root : Name) (positive : Name) (missing : Name) : List String :=
  let nodes := closure env [root] {}
  let all : List Name := nodes.toList
  let producer := ``Li2Lean.P0.CoefficientAssembly.P0CoefficientStepActual
  let producerPresent := match env.find? producer with | some _ => "true" | none => "false"
  let producerReachable := if all.contains producer then "true" else "false"
  let positiveNodes := closure env [positive] {}
  let conditional := closure env [``Li2Lean.li2_half_irrational_of_bridges] {}
  let conditionalLegacy := conditional.filter (fun n =>
    hasPrefix "Li2Lean.Li2Bridges" n || hasPrefix "Li2Bridges" n)
  let missingPresent := match env.find? missing with | some _ => "true" | none => "false"
  let prefixLines := [
    "Li2Lean.P0.Config.CAReceipt",
    "Li2Lean.P0.CAReceiptSlack",
    "Li2Lean.P0DualCertificate",
    "Li2Lean.Li2Bridges",
    "Li2Bridges"
  ].map (fun p =>
    let hits := all.filter (hasPrefix p)
    s!"PREFIX {p} reachable_count={List.length hits}")
  let lines := [s!"ROOT {root}", s!"NODE_COUNT {List.length all}"] ++
    forbiddenLines all ++
    [s!"DEPENDENCY_MODE declaration types + values + encountered local inductive constructors/recursors",
     s!"ACTIVE_COEFFICIENT_PRODUCER {producer} present={producerPresent} reachable_from_root={producerReachable}",
     s!"POSITIVE_CONTROL {positive} reachable_count={List.length positiveNodes.toList}",
     s!"CONDITIONAL_CONTROL Li2Lean.li2_half_irrational_of_bridges reachable_count={List.length conditional.toList} bridge_reachable_count={List.length conditionalLegacy.toList}",
     s!"NEGATIVE_CONTROL {missing} present={missingPresent}"] ++ prefixLines
  lines

elab "release_closure_scan" : command => do
  let env ← getEnv
  for line in reportWithEnv env ``li2_half_irrational
      ``Li2Lean.li2_half_irrational_of_envelope_v2 `Li2Lean.__v5_nonexistent_control do
    logInfo m!"{line}"

end Li2Lean.ReleaseVerification

release_closure_scan
