import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext
import BEDC.GroundCompiler.ChannelEncoding

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

def targetMsameRefl : String :=
  "BEDC.FKernel.Mark.msame_refl"

def targetHsameRefl : String :=
  "BEDC.FKernel.Hist.hsame_refl"

def targetExtStep : String :=
  "BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1"

inductive Family where
  | mark
  | hist
  | ext
  deriving Repr, DecidableEq

def Family.name : Family -> String
  | Family.mark => "mark"
  | Family.hist => "hist"
  | Family.ext => "ext"

def Family.targetKey : Family -> String
  | Family.mark => targetMsameRefl
  | Family.hist => targetHsameRefl
  | Family.ext => targetExtStep

inductive FailKind where
  | cDecode
  | leanDecode
  | semantic
  | missingTarget
  | fixture
  deriving Repr, DecidableEq

def FailKind.name : FailKind -> String
  | FailKind.cDecode => "C-decode"
  | FailKind.leanDecode => "Lean-decode"
  | FailKind.semantic => "semantic"
  | FailKind.missingTarget => "missing-target"
  | FailKind.fixture => "fixture"

structure CheckError where
  kind : FailKind
  caseName : String
  message : String
  deriving Repr

def manifestCase : String :=
  "manifest"

def fail {α : Type} (kind : FailKind) (caseName message : String) :
    Except CheckError α :=
  throw { kind := kind, caseName := caseName, message := message }

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

def parseHeader (kind : String) (line : String) : Except CheckError Nat := do
  let fields := (trim line).splitOn " "
  match fields.filter (fun s => s != "") with
  | [actual, value] =>
      if actual = kind then
        match value.toNat? with
        | some n => pure n
        | none => fail FailKind.fixture manifestCase s!"{kind} count is not a natural number: {value}"
      else
        fail FailKind.fixture manifestCase s!"expected {kind}, got: {line}"
  | _ => fail FailKind.fixture manifestCase s!"malformed {kind} header: {line}"

def parseField? (caseName part : String) : Except CheckError (Option (String × String)) := do
  match (trim part).splitOn "=" with
  | [_] => pure none
  | key :: value :: _ =>
      let key := trim key
      let value := trim value
      if key = "" || value = "" then
        fail FailKind.fixture caseName s!"malformed empty field: {part}"
      else
        pure (some (key, value))
  | [] => pure none

def parseAssertion (line : String) : Except CheckError Assertion := do
  let parts := line.splitOn ";"
  let head <- match parts with
    | [] => fail FailKind.fixture manifestCase "empty assertion line"
    | head :: _ => pure (trim head)
  let fieldParts := match parts with
    | [] => []
    | _ :: rest => rest
  let (name, inputField) <- match head.splitOn ":" with
    | [left, right] =>
        let left := trim left
        if !left.startsWith "case " then
          fail FailKind.fixture manifestCase s!"assertion must start with case: {line}"
        else
          pure (trim (left.drop 5).toString, trim right)
    | _ => fail FailKind.fixture manifestCase s!"malformed assertion head: {line}"
  if name = "" then
    fail FailKind.fixture manifestCase s!"empty case name: {line}"
  let inputPair? <- parseField? name inputField
  let inputPair <- match inputPair? with
    | some field => pure field
    | none => fail FailKind.fixture name s!"first assertion field must be input=: {line}"
  if inputPair.fst != "input" then
    fail FailKind.fixture name s!"first assertion field must be input=: {line}"
  let parsedFields <- fieldParts.mapM (parseField? name)
  let fields := parsedFields.filterMap id
  pure { name := name, input := inputPair.snd, fields := fields }

def parseManifest (content : String) : Except CheckError Manifest := do
  let lines := (content.lines).toList.map String.Slice.toString
  let lines := lines.filter nonCommentLine
  match lines with
  | prodHeader :: rest =>
      let productionCount <- parseHeader "PRODUCTIONS" prodHeader
      if rest.length < productionCount + 1 then
        fail FailKind.fixture manifestCase "manifest ended before ASSERTIONS header"
      let afterProductions := rest.drop productionCount
      let assertionsHeader <- match afterProductions with
        | h :: _ => pure h
        | [] => fail FailKind.fixture manifestCase "missing ASSERTIONS header"
      let assertionCount <- parseHeader "ASSERTIONS" assertionsHeader
      let assertionLines := afterProductions.drop 1
      if assertionLines.length != assertionCount then
        fail FailKind.fixture manifestCase s!"ASSERTIONS declared {assertionCount}, found {assertionLines.length}"
      let assertions <- assertionLines.mapM parseAssertion
      pure {
        productions := productionCount,
        assertionsDeclared := assertionCount,
        assertions := assertions
      }
  | [] => fail FailKind.fixture manifestCase "empty manifest"

def familyOfPath (path : String) : Except CheckError Family := do
  if path.endsWith "rule110/manifests/mark/msame_refl.enum.ct" ||
      path.endsWith "manifests/mark/msame_refl.enum.ct" then
    pure Family.mark
  else if path.endsWith "rule110/manifests/hist/hsame_refl.enum.ct" ||
      path.endsWith "manifests/hist/hsame_refl.enum.ct" then
    pure Family.hist
  else if path.endsWith "rule110/manifests/ext/ext_step.enum.ct" ||
      path.endsWith "manifests/ext/ext_step.enum.ct" then
    pure Family.ext
  else
    fail FailKind.missingTarget manifestCase s!"unsupported manifest path: {path}"

def fieldValue? (fields : List (String × String)) (key : String) : Option String :=
  match fields with
  | [] => none
  | (k, v) :: rest => if k = key then some v else fieldValue? rest key

def fieldAtom (value : String) : String :=
  match (trim value).splitOn " " with
  | atom :: _ => atom
  | [] => ""

def fieldValueAny? (fields : List (String × String)) (keys : List String) : Option String :=
  match keys with
  | [] => none
  | key :: rest =>
      match fieldValue? fields key with
      | some value => some value
      | none => fieldValueAny? fields rest

def validateReflexiveYes (a : Assertion) : Except CheckError Unit := do
  match fieldValueAny? a.fields ["expected_reflexive", "expect_reflexive"] with
  | some value =>
      if fieldAtom value = "yes" then
        pure ()
      else
        fail FailKind.fixture a.name s!"reflexive expectation must be yes, got {value}"
  | none => fail FailKind.fixture a.name "missing reflexive expectation field"

def validateExtHolds (a : Assertion) : Except CheckError Bool := do
  match fieldValue? a.fields "ext_holds" with
  | some value =>
      match fieldAtom value with
      | "yes" => pure true
      | "no" => pure false
      | atom => fail FailKind.fixture a.name s!"ext_holds must be yes or no, got {atom}"
  | none => fail FailKind.fixture a.name "missing ext_holds field"

def bitStringToDisplay (caseName bits : String) :
    Except CheckError (List DisplayAlphabet) := do
  bits.toList.mapM fun
    | '0' => pure BMark.b0
    | '1' => pure BMark.b1
    | c => fail FailKind.leanDecode caseName s!"non-binary input character: {c}"

def parseBMarkEvent (caseName : String) (w : RawEvent) :
    Except CheckError BMark :=
  match w with
  | [BMark.b0] => pure BMark.b0
  | [BMark.b1] => pure BMark.b1
  | [] => fail FailKind.leanDecode caseName "event is empty, not a BMark payload"
  | _ => fail FailKind.leanDecode caseName "event has more than one payload symbol, not a BMark payload"

def parseBHistEvent : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: rest => BHist.e0 (parseBHistEvent rest)
  | BMark.b1 :: rest => BHist.e1 (parseBHistEvent rest)

def decodeTwoBMarks (caseName bits : String) :
    Except CheckError (BMark × BMark) := do
  let symbols <- bitStringToDisplay caseName bits
  let first <- match DecEvent symbols with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode first event"
  let second <- match DecEvent first.snd with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode second event"
  match second.snd with
  | [] =>
      let m <- parseBMarkEvent caseName first.fst
      let n <- parseBMarkEvent caseName second.fst
      pure (m, n)
  | _ :: _ => fail FailKind.leanDecode caseName "trailing input after two events"

def decodeTwoBHists (caseName bits : String) :
    Except CheckError (BHist × BHist) := do
  let symbols <- bitStringToDisplay caseName bits
  let first <- match DecEvent symbols with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode first event"
  let second <- match DecEvent first.snd with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode second event"
  match second.snd with
  | [] =>
      pure (parseBHistEvent first.fst, parseBHistEvent second.fst)
  | _ :: _ => fail FailKind.leanDecode caseName "trailing input after two events"

def decodeExtTriple (caseName bits : String) :
    Except CheckError (BHist × BMark × BHist) := do
  let symbols <- bitStringToDisplay caseName bits
  let source <- match DecEvent symbols with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode source history event"
  let mark <- match DecEvent source.snd with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode mark event"
  let result <- match DecEvent mark.snd with
    | some pair => pure pair
    | none => fail FailKind.leanDecode caseName "could not decode result history event"
  match result.snd with
  | [] =>
      let m <- parseBMarkEvent caseName mark.fst
      pure (parseBHistEvent source.fst, m, parseBHistEvent result.fst)
  | _ :: _ => fail FailKind.leanDecode caseName "trailing input after three events"

def markLabel : BMark -> String
  | BMark.b0 => "b0"
  | BMark.b1 => "b1"

def histLabel : BHist -> String
  | BHist.Empty => "Empty"
  | BHist.e0 h => "e0(" ++ histLabel h ++ ")"
  | BHist.e1 h => "e1(" ++ histLabel h ++ ")"

def extResult (h : BHist) : BMark -> BHist
  | BMark.b0 => BHist.e0 h
  | BMark.b1 => BHist.e1 h

theorem msameReflGroundOk (m n : BMark) (h : m = n) : msame m n := by
  cases h
  exact msame_refl m

theorem hsameReflGroundOk (h k : BHist) (same : h = k) : hsame h k := by
  cases same
  exact hsame_refl h

theorem extPositiveGroundOk (h : BHist) (m : BMark) (r : BHist)
    (result : r = extResult h m) : Ext h m r := by
  cases result
  cases m
  · exact Ext.e0 h
  · exact Ext.e1 h

theorem extNegativeGroundOk (h : BHist) (m : BMark) (r : BHist)
    (result : Not (r = extResult h m)) : Not (Ext h m r) := by
  intro hx
  apply result
  cases hx
  · rfl
  · rfl

def checkMsameRefl (path : String) (a : Assertion) :
    Except CheckError String := do
  validateReflexiveYes a
  let (m, n) <- decodeTwoBMarks a.name a.input
  if h : m = n then
    let _proof : msame m n := msameReflGroundOk m n h
    pure s!"PASS path={path} family=mark case={a.name} decoded=({markLabel m},{markLabel n}) target={targetMsameRefl}"
  else
    fail FailKind.semantic a.name s!"decoded ({markLabel m},{markLabel n}); expected reflexive pair"

def checkHsameRefl (path : String) (a : Assertion) :
    Except CheckError String := do
  validateReflexiveYes a
  let (h, k) <- decodeTwoBHists a.name a.input
  if same : h = k then
    let _proof : hsame h k := hsameReflGroundOk h k same
    pure s!"PASS path={path} family=hist case={a.name} decoded=({histLabel h},{histLabel k}) target={targetHsameRefl}"
  else
    fail FailKind.semantic a.name s!"decoded ({histLabel h},{histLabel k}); expected reflexive pair"

def checkExtStep (path : String) (a : Assertion) :
    Except CheckError String := do
  let expected <- validateExtHolds a
  let (h, m, r) <- decodeExtTriple a.name a.input
  if result : r = extResult h m then
    let _proof : Ext h m r := extPositiveGroundOk h m r result
    if expected then
      pure s!"PASS path={path} family=ext case={a.name} decoded=({histLabel h},{markLabel m},{histLabel r}) ext_holds=yes target={targetExtStep}"
    else
      fail FailKind.semantic a.name s!"decoded ({histLabel h},{markLabel m},{histLabel r}); Ext holds but manifest expected no"
  else
    let _proof : Not (Ext h m r) := extNegativeGroundOk h m r result
    if expected then
      fail FailKind.semantic a.name s!"decoded ({histLabel h},{markLabel m},{histLabel r}); Ext does not hold but manifest expected yes"
    else
      pure s!"PASS path={path} family=ext case={a.name} decoded=({histLabel h},{markLabel m},{histLabel r}) ext_holds=no target={targetExtStep}"

partial def hasDuplicateCase : List String -> Bool
  | [] => false
  | name :: rest => rest.contains name || hasDuplicateCase rest

def checkManifest (path : String) (manifest : Manifest) :
    Except CheckError (List String) := do
  let family <- familyOfPath path
  if manifest.productions != 0 then
    fail FailKind.fixture manifestCase s!"{family.name} manifest must have PRODUCTIONS 0, got {manifest.productions}"
  if manifest.assertions.length != manifest.assertionsDeclared then
    fail FailKind.fixture manifestCase s!"assertion count mismatch: declared {manifest.assertionsDeclared}, parsed {manifest.assertions.length}"
  if hasDuplicateCase (manifest.assertions.map (·.name)) then
    fail FailKind.fixture manifestCase "duplicate assertion case name"
  match family with
  | Family.mark => manifest.assertions.mapM (checkMsameRefl path)
  | Family.hist => manifest.assertions.mapM (checkHsameRefl path)
  | Family.ext => manifest.assertions.mapM (checkExtStep path)

def registeredManifests : List String := [
  "../rule110/manifests/mark/msame_refl.enum.ct",
  "../rule110/manifests/hist/hsame_refl.enum.ct",
  "../rule110/manifests/ext/ext_step.enum.ct"
]

def usage : String :=
  "usage: cd lean4 && lake exe rule110-cross-check [manifest.enum.ct]..."

def formatFail (path : String) (e : CheckError) : String :=
  s!"FAIL kind={e.kind.name} path={path} case={e.caseName} message={e.message}"

def runOne (path : String) : IO UInt32 := do
  try
    let content <- IO.FS.readFile path
    match parseManifest content >>= checkManifest path with
    | Except.ok lines =>
        for line in lines do
          IO.println line
        pure 0
    | Except.error e =>
        IO.eprintln (formatFail path e)
        pure 1
  catch e =>
    IO.eprintln (formatFail path {
      kind := FailKind.fixture,
      caseName := manifestCase,
      message := e.toString
    })
    pure 1

partial def runMany : List String -> IO UInt32
  | [] => pure 0
  | path :: rest => do
      let code <- runOne path
      let restCode <- runMany rest
      if code == 0 && restCode == 0 then pure 0 else pure 1

def run (args : List String) : IO UInt32 := do
  match args with
  | [] => runMany registeredManifests
  | _ => runMany args

end BEDC.Rule110CrossCheck

def main (args : List String) : IO UInt32 :=
  BEDC.Rule110CrossCheck.run args
