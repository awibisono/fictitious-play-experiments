import Karlin.FaithfulV15

open Lean in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if owner.toString.startsWith "Karlin." then
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom"
        | _ => "other"
      let value := match info with
        | .defnInfo v => toString (hash v.value)
        | _ => ""
      let row := Json.mkObj [("name", toJson name.toString),
        ("module", toJson owner.toString), ("kind", toJson kind),
        ("type", toJson (toString (hash info.type))), ("value", toJson value),
        ("unsafe", toJson info.isUnsafe)]
      IO.println row.compress
