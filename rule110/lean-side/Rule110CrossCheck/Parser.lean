
namespace BEDC.Rule110CrossCheck

structure Assertion where
  name : String
  input : String
  fields : List (String × String)
  deriving Repr

structure Manifest where
  productions : Nat
  assertionsDeclared : Nat
  assertions : List Assertion
  deriving Repr

def trim (s : String) : String :=
  s.trimAscii.toString

def nonCommentLine (s : String) : Bool :=
  let t := trim s
  t != "" && !t.startsWith "#"

def parseHeader (kind : String) (line : String) : Except String Nat := do
  let fields := (trim line).splitOn " "
  match fields.filter (fun s => s != "") with
  | [actual, value] =>
      if actual = kind then
        match value.toNat? with
        | some n => pure n
        | none => throw s!"{kind} count is not a natural number: {value}"
      else
        throw s!"expected {kind}, got: {line}"
  | _ => throw s!"malformed {kind} header: {line}"

def parseField? (part : String) : Except String (Option (String × String)) := do
  match (trim part).splitOn "=" with
  | [_] => pure none
  | key :: value :: _ =>
      let key := trim key
      let value := trim value
      if key = "" || value = "" then
        throw s!"malformed empty field: {part}"
      else
        pure (some (key, value))
  | [] => pure none

def parseAssertion (line : String) : Except String Assertion := do
  let parts := line.splitOn ";"
  let head <- match parts with
    | [] => throw "empty assertion line"
    | head :: _ => pure (trim head)
  let fieldParts := match parts with
    | [] => []
    | _ :: rest => rest
  let (name, inputField) <- match head.splitOn ":" with
    | [left, right] =>
        let left := trim left
        if !left.startsWith "case " then
          throw s!"assertion must start with case: {line}"
        else
          pure (trim (left.drop 5).toString, trim right)
    | _ => throw s!"malformed assertion head: {line}"
  if name = "" then
    throw s!"empty case name: {line}"
  let inputPair? <- parseField? inputField
  let inputPair <- match inputPair? with
    | some field => pure field
    | none => throw s!"first assertion field must be input=: {line}"
  if inputPair.fst != "input" then
    throw s!"first assertion field must be input=: {line}"
  let parsedFields <- fieldParts.mapM parseField?
  pure { name := name, input := inputPair.snd, fields := parsedFields.filterMap id }

def parseManifest (content : String) : Except String Manifest := do
  let lines := (content.lines).toList.map String.Slice.toString
  let lines := lines.filter nonCommentLine
  match lines with
  | prodHeader :: rest =>
      let productionCount <- parseHeader "PRODUCTIONS" prodHeader
      if rest.length < productionCount + 1 then
        throw "manifest ended before ASSERTIONS header"
      let afterProductions := rest.drop productionCount
      let assertionsHeader <- match afterProductions with
        | h :: _ => pure h
        | [] => throw "missing ASSERTIONS header"
      let assertionCount <- parseHeader "ASSERTIONS" assertionsHeader
      let assertionLines := afterProductions.drop 1
      if assertionLines.length != assertionCount then
        throw s!"ASSERTIONS declared {assertionCount}, found {assertionLines.length}"
      let assertions <- assertionLines.mapM parseAssertion
      pure { productions := productionCount, assertionsDeclared := assertionCount, assertions := assertions }
  | [] => throw "empty manifest"

end BEDC.Rule110CrossCheck
