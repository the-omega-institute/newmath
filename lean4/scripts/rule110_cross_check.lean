import BEDC.FKernel.Mark
import BEDC.GroundCompiler.ChannelEncoding

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

def targetMsameRefl : String :=
  "BEDC.FKernel.Mark.msame_refl"

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

def parseField (part : String) : Except String (String × String) := do
  match (trim part).splitOn "=" with
  | [key, value] =>
      let key := trim key
      let value := trim value
      if key = "" || value = "" then
        throw s!"malformed empty field: {part}"
      else
        pure (key, value)
  | _ => throw s!"malformed field: {part}"

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
  let inputPair <- parseField inputField
  if inputPair.fst != "input" then
    throw s!"first assertion field must be input=: {line}"
  let fields <- fieldParts.mapM parseField
  pure { name := name, input := inputPair.snd, fields := fields }

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
      pure {
        productions := productionCount,
        assertionsDeclared := assertionCount,
        assertions := assertions
      }
  | [] => throw "empty manifest"

def ensureMsameReflPath (path : String) : Except String Unit := do
  if path.endsWith "rule110/manifests/mark/msame_refl.enum.ct" ||
      path.endsWith "manifests/mark/msame_refl.enum.ct" then
    pure ()
  else
    throw s!"unsupported manifest path for this POC: {path}"

def fieldValue? (fields : List (String × String)) (key : String) : Option String :=
  match fields with
  | [] => none
  | (k, v) :: rest => if k = key then some v else fieldValue? rest key

def validateMsameFields (a : Assertion) : Except String Unit := do
  match fieldValue? a.fields "expected_reflexive" with
  | some "yes" => pure ()
  | some value => throw s!"case {a.name}: expected_reflexive must be yes, got {value}"
  | none => throw s!"case {a.name}: missing expected_reflexive=yes"

def bitStringToDisplay (bits : String) : Except String (List DisplayAlphabet) := do
  bits.toList.mapM fun
    | '0' => pure BMark.b0
    | '1' => pure BMark.b1
    | c => throw s!"non-binary input character: {c}"

def parseBMarkEvent (w : RawEvent) : Except String BMark :=
  match w with
  | [BMark.b0] => pure BMark.b0
  | [BMark.b1] => pure BMark.b1
  | [] => throw "event is empty, not a BMark payload"
  | _ => throw "event has more than one payload symbol, not a BMark payload"

def decodeTwoBMarks (bits : String) : Except String (BMark × BMark) := do
  let symbols <- bitStringToDisplay bits
  let first <- match DecEvent symbols with
    | some pair => pure pair
    | none => throw "could not decode first event"
  let second <- match DecEvent first.snd with
    | some pair => pure pair
    | none => throw "could not decode second event"
  match second.snd with
  | [] =>
      let m <- parseBMarkEvent first.fst
      let n <- parseBMarkEvent second.fst
      pure (m, n)
  | _ :: _ => throw "trailing input after two events"

def markLabel : BMark -> String
  | BMark.b0 => "b0"
  | BMark.b1 => "b1"

theorem msameReflGroundOk (m n : BMark) (h : m = n) : msame m n := by
  cases h
  exact msame_refl m

def checkMsameRefl (a : Assertion) : Except String String := do
  validateMsameFields a
  let (m, n) <- decodeTwoBMarks a.input
  if h : m = n then
    let _proof : msame m n := msameReflGroundOk m n h
    pure s!"PASS msame_refl {a.name} ({markLabel m},{markLabel n}) -> {targetMsameRefl}"
  else
    throw s!"case {a.name}: decoded ({markLabel m},{markLabel n}); expected reflexive pair"

partial def hasDuplicateCase : List String -> Bool
  | [] => false
  | name :: rest => rest.contains name || hasDuplicateCase rest

def checkManifest (path : String) (manifest : Manifest) : Except String (List String) := do
  ensureMsameReflPath path
  if manifest.productions != 0 then
    throw s!"msame_refl.enum.ct must have PRODUCTIONS 0, got {manifest.productions}"
  if manifest.assertions.length != manifest.assertionsDeclared then
    throw s!"assertion count mismatch: declared {manifest.assertionsDeclared}, parsed {manifest.assertions.length}"
  if hasDuplicateCase (manifest.assertions.map (·.name)) then
    throw "duplicate assertion case name"
  manifest.assertions.mapM checkMsameRefl

def usage : String :=
  "usage: cd lean4 && lake env lean --run scripts/rule110_cross_check.lean ../rule110/manifests/mark/msame_refl.enum.ct"

def run (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let content <- IO.FS.readFile path
      match parseManifest content >>= checkManifest path with
      | Except.ok lines =>
          for line in lines do
            IO.println line
          pure 0
      | Except.error e =>
          IO.eprintln s!"FAIL {path}: {e}"
          pure 1
  | _ =>
      IO.eprintln usage
      pure 1

end BEDC.Rule110CrossCheck

def main (args : List String) : IO UInt32 :=
  BEDC.Rule110CrossCheck.run args
