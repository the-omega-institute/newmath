import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.FKernel.Ask
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Package
import BEDC.FKernel.Gap
import BEDC.FKernel.NameCert
import BEDC.FKernel.Settled
import BEDC.GroundCompiler.ChannelEncoding

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.FKernel.Package
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

deriving instance BEq for BEDC.GroundCompiler.EventFlow.DisplayAlphabet

def markEq (a b : BMark) : Bool :=
  match a, b with
  | BMark.b0, BMark.b0 => true
  | BMark.b1, BMark.b1 => true
  | _, _ => false

def rawEventEq : RawEvent -> RawEvent -> Bool
  | [], [] => true
  | a :: as, b :: bs => markEq a b && rawEventEq as bs
  | _, _ => false

abbrev ProbeNat := Nat
abbrev EvidenceBit := BMark

def histDepth : BHist -> Nat
  | BHist.Empty => 0
  | BHist.e0 h => Nat.succ (histDepth h)
  | BHist.e1 h => Nat.succ (histDepth h)

def appendHist : BHist -> BHist -> BHist :=
  BEDC.FKernel.Cont.append

def extResult (h : BHist) : BMark -> BHist
  | BMark.b0 => BHist.e0 h
  | BMark.b1 => BHist.e1 h

def askExpected (p : Nat) (h : BHist) : BMark :=
  if (p + histDepth h) % 2 = 0 then BMark.b0 else BMark.b1

instance parityAskSetup : AskSetup where
  ProbeName := Nat
  Evidence := BMark
  Ask := fun p h m ev => m = askExpected p h ∧ ev = askExpected p h

instance signaturePackageSetup : PackageSetup :=
  BEDC.FKernel.Package.SignaturePackageSetup

instance boundedDomainSetup : DomainSetup where
  Domain := Nat
  InDom := fun bound h => histDepth h <= bound

def targetMsameRefl : String := "BEDC.FKernel.Mark.msame_refl"
def targetMsameSymm : String := "BEDC.FKernel.Mark.msame_symm"
def targetMsameTrans : String := "BEDC.FKernel.Mark.msame_trans"
def targetMsameNoConfusion : String := "BEDC.FKernel.Mark.msame_no_confusion"
def targetHsameRefl : String := "BEDC.FKernel.Hist.hsame_refl"
def targetHsameSymm : String := "BEDC.FKernel.Hist.hsame_symm"
def targetHsameTrans : String := "BEDC.FKernel.Hist.hsame_trans"
def targetHsameEmpty : String := "BEDC.FKernel.Hist.hsame_empty_inversion/BEDC.FKernel.Hist.hsame_empty_iff"
def targetHsameDistinct : String := "BEDC.FKernel.Hist.hsame_no_confusion"
def targetExtStep : String := "BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1"
def targetCont : String := "BEDC.FKernel.Cont.Cont"
def targetSigRel : String := "BEDC.FKernel.Sig.SigRel"
def targetSameSig : String := "BEDC.FKernel.Sig.SameSig"
def targetBundleLength : String := "BEDC.FKernel.Bundle length/append theorem family"
def targetBundleMembership : String := "BEDC.FKernel.Bundle membership/append theorem family"
def targetUnary : String := "BEDC.FKernel.Unary.UnaryHistory/UnaryCont"
def targetAsk : String := "BEDC.FKernel.Ask.Ask"
def targetExternalBinary : String := "BEDC.FKernel.ExternalBinary.append"
def targetGap : String := "BEDC.FKernel.Gap.InGapSig/CompGap fixture"
def targetPackage : String := "BEDC.FKernel.Package.TokIntro/psame"
def targetNameCert : String := "BEDC.FKernel.NameCert fixture"
def targetSettled : String := "BEDC.FKernel.Settled.SettledKernelCriterion projections"

inductive Family where
  | markRefl
  | markSymm
  | markTrans
  | markNoConfusion
  | histRefl
  | histSymm
  | histTrans
  | histEmpty
  | histDistinct
  | ext
  | cont
  | sigRel
  | sameSig
  | bundleLength
  | bundleMembership
  | unary
  | ask
  | externalBinary
  | gap
  | package
  | nameCert
  | settled
  deriving Repr, DecidableEq

def Family.name : Family -> String
  | .markRefl => "mark/msame_refl"
  | .markSymm => "mark/msame_symm"
  | .markTrans => "mark/msame_trans"
  | .markNoConfusion => "mark/msame_no_confusion"
  | .histRefl => "hist/hsame_refl"
  | .histSymm => "hist/hsame_symm"
  | .histTrans => "hist/hsame_trans"
  | .histEmpty => "hist/hsame_empty_inversion"
  | .histDistinct => "hist/hsame_constructor_distinct"
  | .ext => "ext/ext_step"
  | .cont => "cont/cont_basic"
  | .sigRel => "sig/sigrel_basic"
  | .sameSig => "sig/samesig_equiv"
  | .bundleLength => "bundle/bundle_length"
  | .bundleMembership => "bundle/bundle_membership"
  | .unary => "unary/unary_basic"
  | .ask => "ask/ask_basic"
  | .externalBinary => "external_binary/external_binary_basic"
  | .gap => "gap/gap_basic"
  | .package => "package/package_basic"
  | .nameCert => "name_cert/name_cert_basic"
  | .settled => "settled/settled_basic"

def Family.targetKey : Family -> String
  | .markRefl => targetMsameRefl
  | .markSymm => targetMsameSymm
  | .markTrans => targetMsameTrans
  | .markNoConfusion => targetMsameNoConfusion
  | .histRefl => targetHsameRefl
  | .histSymm => targetHsameSymm
  | .histTrans => targetHsameTrans
  | .histEmpty => targetHsameEmpty
  | .histDistinct => targetHsameDistinct
  | .ext => targetExtStep
  | .cont => targetCont
  | .sigRel => targetSigRel
  | .sameSig => targetSameSig
  | .bundleLength => targetBundleLength
  | .bundleMembership => targetBundleMembership
  | .unary => targetUnary
  | .ask => targetAsk
  | .externalBinary => targetExternalBinary
  | .gap => targetGap
  | .package => targetPackage
  | .nameCert => targetNameCert
  | .settled => targetSettled

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

def registeredManifestSpecs : List (String × Family) := [
  ("manifests/mark/msame_refl.enum.ct", .markRefl),
  ("manifests/mark/msame_symm.enum.ct", .markSymm),
  ("manifests/mark/msame_trans.enum.ct", .markTrans),
  ("manifests/mark/msame_no_confusion.enum.ct", .markNoConfusion),
  ("manifests/hist/hsame_refl.enum.ct", .histRefl),
  ("manifests/hist/hsame_symm.enum.ct", .histSymm),
  ("manifests/hist/hsame_trans.enum.ct", .histTrans),
  ("manifests/hist/hsame_empty_inversion.enum.ct", .histEmpty),
  ("manifests/hist/hsame_constructor_distinct.enum.ct", .histDistinct),
  ("manifests/ext/ext_step.enum.ct", .ext),
  ("manifests/cont/cont_basic.enum.ct", .cont),
  ("manifests/sig/sigrel_basic.enum.ct", .sigRel),
  ("manifests/sig/samesig_equiv.enum.ct", .sameSig),
  ("manifests/bundle/bundle_length.enum.ct", .bundleLength),
  ("manifests/bundle/bundle_membership.enum.ct", .bundleMembership),
  ("manifests/unary/unary_basic.enum.ct", .unary),
  ("manifests/ask/ask_basic.enum.ct", .ask),
  ("manifests/external_binary/external_binary_basic.enum.ct", .externalBinary),
  ("manifests/gap/gap_basic.enum.ct", .gap),
  ("manifests/package/package_basic.enum.ct", .package),
  ("manifests/name_cert/name_cert_basic.enum.ct", .nameCert),
  ("manifests/settled/settled_basic.enum.ct", .settled)
]

def familyOfPath (path : String) : Except String Family := do
  match registeredManifestSpecs.find? (fun spec => path.endsWith spec.fst) with
  | some spec => pure spec.snd
  | none => throw s!"unsupported manifest path: {path}"

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

def expectAtom (a : Assertion) (keys : List String) : Except String String := do
  match fieldValueAny? a.fields keys with
  | some value => pure (fieldAtom value)
  | none => throw s!"case {a.name}: missing expectation field among {keys}"

def expectBool (a : Assertion) (keys : List String) : Except String Bool := do
  match (← expectAtom a keys) with
  | "yes" => pure true
  | "no" => pure false
  | atom => throw s!"case {a.name}: expected yes/no field, got {atom}"

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

def parseBitEvent (w : RawEvent) : Except String Bool :=
  match w with
  | [BMark.b0] => pure false
  | [BMark.b1] => pure true
  | _ => throw "event is not a one-bit payload"

def parseTwoBitEvent (w : RawEvent) : Except String (Bool × Bool) :=
  match w with
  | [a, b] => pure (markEq a BMark.b1, markEq b BMark.b1)
  | _ => throw "event is not a two-bit payload"

def parseBHistEvent : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: rest => BHist.e0 (parseBHistEvent rest)
  | BMark.b1 :: rest => BHist.e1 (parseBHistEvent rest)

def parseUnaryNatEvent (w : RawEvent) : Except String Nat :=
  match w.reverse with
  | BMark.b1 :: rest =>
      if rest.all (fun m => markEq m BMark.b0) then pure rest.length
      else throw "unary nat event has nonzero prefix"
  | _ => throw "unary nat event must be nonempty and end with b1"

def decodeEvent (symbols : List DisplayAlphabet) : Except String (RawEvent × List DisplayAlphabet) :=
  match DecEvent symbols with
  | some pair => pure pair
  | none => throw "could not decode event"

partial def decodeAllEventsFuel : Nat -> List DisplayAlphabet -> Except String (List RawEvent)
  | 0, [] => pure []
  | 0, _ :: _ => throw "event stream decoder exhausted fuel"
  | _ + 1, [] => pure []
  | fuel + 1, symbols => do
      let (event, rest) <- decodeEvent symbols
      let tail <- decodeAllEventsFuel fuel rest
      pure (event :: tail)

def decodeAllEvents (bits : String) : Except String (List RawEvent) := do
  let symbols <- bitStringToDisplay bits
  decodeAllEventsFuel symbols.length symbols

def decodeExactlyEvents (bits : String) (n : Nat) : Except String (List RawEvent) := do
  let events <- decodeAllEvents bits
  if events.length = n then pure events
  else throw s!"expected {n} event(s), decoded {events.length}"

def decodeTwoWith (bits : String) (parse : RawEvent -> Except String α) : Except String (α × α) := do
  match (← decodeExactlyEvents bits 2) with
  | [a, b] => pure (← parse a, ← parse b)
  | _ => throw "internal arity mismatch"

def decodeThreeWith (bits : String) (parse : RawEvent -> Except String α) : Except String (α × α × α) := do
  match (← decodeExactlyEvents bits 3) with
  | [a, b, c] => pure (← parse a, ← parse b, ← parse c)
  | _ => throw "internal arity mismatch"

def decodeTwoBMarks (bits : String) : Except String (BMark × BMark) :=
  decodeTwoWith bits parseBMarkEvent

def decodeThreeBMarks (bits : String) : Except String (BMark × BMark × BMark) :=
  decodeThreeWith bits parseBMarkEvent

def decodeTwoBHists (bits : String) : Except String (BHist × BHist) :=
  decodeTwoWith bits (fun e => pure (parseBHistEvent e))

def decodeThreeBHists (bits : String) : Except String (BHist × BHist × BHist) :=
  decodeThreeWith bits (fun e => pure (parseBHistEvent e))

def decodeExtTriple (bits : String) : Except String (BHist × BMark × BHist) := do
  match (← decodeExactlyEvents bits 3) with
  | [source, mark, result] =>
      pure (parseBHistEvent source, ← parseBMarkEvent mark, parseBHistEvent result)
  | _ => throw "internal arity mismatch"

def markLabel : BMark -> String
  | BMark.b0 => "b0"
  | BMark.b1 => "b1"

def histLabel : BHist -> String
  | BHist.Empty => "Empty"
  | BHist.e0 h => "e0(" ++ histLabel h ++ ")"
  | BHist.e1 h => "e1(" ++ histLabel h ++ ")"

def natListLabel : List Nat -> String
  | [] => "[]"
  | x :: xs => "[" ++ toString x ++ xs.foldl (fun acc y => acc ++ "," ++ toString y) "" ++ "]"

def parseBundleTerminatedBy (events : List RawEvent) (isEnd : RawEvent -> Bool) :
    Except String (List Nat × List RawEvent) := do
  let rec go (acc : List Nat) : List RawEvent -> Except String (List Nat × List RawEvent)
    | [] => throw "unterminated bundle"
    | event :: rest =>
        if isEnd event then
          pure (acc.reverse, rest)
        else do
          let probe <- parseUnaryNatEvent event
          go (probe :: acc) rest
  go [] events

def parseEmptyTerminatedBundle (events : List RawEvent) : Except String (List Nat × List RawEvent) :=
  parseBundleTerminatedBy events (fun e => rawEventEq e [])

def parseReservedTerminatedBundle (events : List RawEvent) : Except String (List Nat × List RawEvent) :=
  parseBundleTerminatedBy events (fun e => rawEventEq e [BMark.b1, BMark.b1])

def parseBundleFor (family : Family) (events : List RawEvent) : Except String (List Nat × List RawEvent) :=
  match family with
  | .bundleLength | .bundleMembership | .package => parseReservedTerminatedBundle events
  | _ => parseEmptyTerminatedBundle events

def parseNBundlesFor (family : Family) : Nat -> List RawEvent -> Except String (List (List Nat) × List RawEvent)
  | 0, events => pure ([], events)
  | n + 1, events => do
      let (bundle, rest) <- parseBundleFor family events
      let (tail, final) <- parseNBundlesFor family n rest
      pure (bundle :: tail, final)

def parseBHistFromEvents (events : List RawEvent) : Except String (BHist × List RawEvent) :=
  match events with
  | event :: rest => pure (parseBHistEvent event, rest)
  | [] => throw "expected BHist event"

def parseNatFromEvents (events : List RawEvent) : Except String (Nat × List RawEvent) :=
  match events with
  | event :: rest => do
      let n <- parseUnaryNatEvent event
      pure (n, rest)
  | [] => throw "expected unary nat event"

def parseBMarkFromEvents (events : List RawEvent) : Except String (BMark × List RawEvent) :=
  match events with
  | event :: rest => do
      let m <- parseBMarkEvent event
      pure (m, rest)
  | [] => throw "expected mark event"

def parseTwoBitsFromEvents (events : List RawEvent) : Except String ((Bool × Bool) × List RawEvent) :=
  match events with
  | event :: rest => do
      let bits <- parseTwoBitEvent event
      pure (bits, rest)
  | [] => throw "expected two-bit relation event"

def requireNoRest (rest : List RawEvent) : Except String Unit :=
  match rest with
  | [] => pure ()
  | _ => throw s!"trailing input: {rest.length} event(s)"

def bundleAppendList (a b : List Nat) : List Nat := a ++ b

def bundleContains (p : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs => x == p || bundleContains p xs

def sigResult (bundle : List Nat) (h : BHist) : BHist :=
  bundle.foldr (fun p acc => extResult acc (askExpected p h)) BHist.Empty

def sameSigFixture (bundle : List Nat) (h k : BHist) : Bool :=
  sigResult bundle h == sigResult bundle k

def unaryHistoryBool : BHist -> Bool
  | BHist.Empty => true
  | BHist.e1 h => unaryHistoryBool h
  | BHist.e0 _ => false

def tokIntroBool (s p : BHist) : Bool := s == p

def psameBool (s t p q : BHist) : Bool :=
  tokIntroBool s p && tokIntroBool t q && s == t

def boolExpected (truth : Bool) (expected : Bool) : Except String Unit :=
  if truth == expected then pure () else throw s!"semantic mismatch: computed {truth}, expected {expected}"

def passLine (path : String) (family : Family) (a : Assertion) (decoded : String) (polarity : String := "") : String :=
  let pol := if polarity = "" then "" else s!" {polarity}"
  s!"PASS path={path} family={family.name} case={a.name} decoded={decoded}{pol} target={family.targetKey}"

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

theorem contPositiveGroundOk (h k r : BHist) (result : r = appendHist h k) :
    BEDC.FKernel.Cont.Cont h k r := by
  exact BEDC.FKernel.Cont.cont_intro result

theorem contNegativeGroundOk (h k r : BHist) (result : Not (r = appendHist h k)) :
    Not (BEDC.FKernel.Cont.Cont h k r) := by
  intro hc
  exact result (Iff.mp BEDC.FKernel.Cont.cont_iff_append hc)

theorem askPositiveGroundOk (p : Nat) (h : BHist) (m ev : BMark)
    (hm : m = askExpected p h) (he : ev = askExpected p h) :
    Ask p h m ev := by
  exact And.intro hm he

theorem askNegativeGroundOk (p : Nat) (h : BHist) (m ev : BMark)
    (bad : Not (m = askExpected p h ∧ ev = askExpected p h)) :
    Not (Ask p h m ev) := by
  exact bad

theorem sigEmptyGroundOk (h r : BHist) (hr : r = BHist.Empty) :
    SigRel (ProbeBundle.Bnil : ProbeBundle Nat) h r := by
  cases hr
  exact SigRel.empty h

theorem unaryPositiveGroundOk (h : BHist) (u : unaryHistoryBool h = true) : UnaryHistory h := by
  induction h with
  | Empty => exact True.intro
  | e0 h => cases u
  | e1 h ih => exact ih u

theorem unaryNegativeGroundOk (h : BHist) (u : unaryHistoryBool h = false) : Not (UnaryHistory h) := by
  induction h with
  | Empty => cases u
  | e0 h => intro uh; exact uh
  | e1 h ih => exact ih u

def checkMarkRefl (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_reflexive", "expect_reflexive"]) != "yes" then
    throw s!"case {a.name}: reflexive expectation must be yes"
  let (m, n) <- decodeTwoBMarks a.input
  if h : m = n then
    let _proof : msame m n := msameReflGroundOk m n h
    pure (passLine path .markRefl a s!"({markLabel m},{markLabel n})")
  else
    throw s!"case {a.name}: decoded ({markLabel m},{markLabel n}); expected reflexive pair"

def checkMarkSymm (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["conclusion_holds"]
  let (m, n) <- decodeTwoBMarks a.input
  let trivial := m == n
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected symm expectation {atom}"
  if h : m = n then
    let _proof : msame n m := msame_symm (msameReflGroundOk m n h)
    pure (passLine path .markSymm a s!"({markLabel m},{markLabel n})" s!"conclusion_holds={expected}")
  else
    pure (passLine path .markSymm a s!"({markLabel m},{markLabel n})" s!"conclusion_holds={expected}")

def checkMarkTrans (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["holds"]
  let (m, n, o) <- decodeThreeBMarks a.input
  let trivial := m == n && n == o
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected trans expectation {atom}"
  pure (passLine path .markTrans a s!"({markLabel m},{markLabel n},{markLabel o})" s!"holds={expected}")

def checkMarkNoConfusion (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_unequal"]) != "yes" then
    throw s!"case {a.name}: expected_unequal must be yes"
  let (m, n) <- decodeTwoBMarks a.input
  if m == n then
    throw s!"case {a.name}: decoded equal marks"
  else
    pure (passLine path .markNoConfusion a s!"({markLabel m},{markLabel n})" "expected_unequal=yes")

def checkHistRefl (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_reflexive", "expect_reflexive"]) != "yes" then
    throw s!"case {a.name}: reflexive expectation must be yes"
  let (h, k) <- decodeTwoBHists a.input
  if same : h = k then
    let _proof : hsame h k := hsameReflGroundOk h k same
    pure (passLine path .histRefl a s!"({histLabel h},{histLabel k})")
  else
    throw s!"case {a.name}: decoded non-reflexive pair"

def checkHistSymm (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["conclusion_holds"]
  let (h, k) <- decodeTwoBHists a.input
  let trivial := h == k
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected symm expectation {atom}"
  pure (passLine path .histSymm a s!"({histLabel h},{histLabel k})" s!"conclusion_holds={expected}")

def checkHistTrans (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["holds"]
  let (h, k, l) <- decodeThreeBHists a.input
  let trivial := h == k && k == l
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected trans expectation {atom}"
  pure (passLine path .histTrans a s!"({histLabel h},{histLabel k},{histLabel l})" s!"holds={expected}")

def checkHistEmpty (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["empty_match"]
  let (h, k) <- decodeTwoBHists a.input
  boolExpected (h == BHist.Empty && k == BHist.Empty) expected
  pure (passLine path .histEmpty a s!"({histLabel h},{histLabel k})" s!"empty_match={if expected then "yes" else "no"}")

def checkHistDistinct (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_unequal"]) != "yes" then
    throw s!"case {a.name}: expected_unequal must be yes"
  let (h, k) <- decodeTwoBHists a.input
  if h == k then
    throw s!"case {a.name}: decoded equal histories"
  else
    pure (passLine path .histDistinct a s!"({histLabel h},{histLabel k})" "expected_unequal=yes")

def checkExtStep (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["ext_holds"]
  let (h, m, r) <- decodeExtTriple a.input
  if result : r = extResult h m then
    let _proof : Ext h m r := extPositiveGroundOk h m r result
    boolExpected true expected
  else
    let _proof : Not (Ext h m r) := extNegativeGroundOk h m r result
    boolExpected false expected
  pure (passLine path .ext a s!"({histLabel h},{markLabel m},{histLabel r})" s!"ext_holds={if expected then "yes" else "no"}")

def checkContLike (family : Family) (field : String) (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a [field]
  let decoded <- try
      let (h, k, r) <- decodeThreeBHists a.input
      if result : r = appendHist h k then
        let _proof : BEDC.FKernel.Cont.Cont h k r := contPositiveGroundOk h k r result
        pure (true, s!"({histLabel h},{histLabel k},{histLabel r})")
      else
        let _proof : Not (BEDC.FKernel.Cont.Cont h k r) := contNegativeGroundOk h k r result
        pure (false, s!"({histLabel h},{histLabel k},{histLabel r})")
    catch _ =>
      pure (false, a.input)
  boolExpected decoded.fst expected
  pure (passLine path family a decoded.snd s!"{field}={if expected then "yes" else "no"}")

def checkSigRel (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["sigrel"]
  let events <- decodeAllEvents a.input
  let (bundle, rest) <- parseBundleFor .sigRel events
  let (h, rest) <- parseBHistFromEvents rest
  let (r, rest) <- parseBHistFromEvents rest
  requireNoRest rest
  let truth := sigResult bundle h == r
  boolExpected truth expected
  pure (passLine path .sigRel a s!"({natListLabel bundle},{histLabel h},{histLabel r})" s!"sigrel={if expected then "yes" else "no"}")

def checkSameSig (path : String) (a : Assertion) : Except String String := do
  let events <- decodeAllEvents a.input
  let (bundle, rest) <- parseBundleFor .sameSig events
  if let some value := fieldValue? a.fields "refl" then
    if fieldAtom value != "yes" then throw s!"case {a.name}: refl must be yes"
    let (h, rest) <- parseBHistFromEvents rest
    let (k, rest) <- parseBHistFromEvents rest
    requireNoRest rest
    boolExpected (h == k && sameSigFixture bundle h k) true
    pure (passLine path .sameSig a s!"({natListLabel bundle},{histLabel h},{histLabel k})" "refl=yes")
  else if let some value := fieldValue? a.fields "symm" then
    let expected := fieldAtom value
    let (h, rest) <- parseBHistFromEvents rest
    let (k, rest) <- parseBHistFromEvents rest
    requireNoRest rest
    let hk := sameSigFixture bundle h k
    let kh := sameSigFixture bundle k h
    match expected with
    | "yes" => boolExpected (hk && kh) true
    | "vacuous" => boolExpected hk false
    | atom => throw s!"case {a.name}: unexpected symm expectation {atom}"
    pure (passLine path .sameSig a s!"({natListLabel bundle},{histLabel h},{histLabel k})" s!"symm={expected}")
  else if let some value := fieldValue? a.fields "trans" then
    let expected := fieldAtom value
    let (h, rest) <- parseBHistFromEvents rest
    let (k, rest) <- parseBHistFromEvents rest
    let (l, rest) <- parseBHistFromEvents rest
    requireNoRest rest
    let hk := sameSigFixture bundle h k
    let kl := sameSigFixture bundle k l
    let hl := sameSigFixture bundle h l
    match expected with
    | "yes" => boolExpected (hk && kl && hl) true
    | "vacuous" => boolExpected (hk && kl) false
    | atom => throw s!"case {a.name}: unexpected trans expectation {atom}"
    pure (passLine path .sameSig a s!"({natListLabel bundle},{histLabel h},{histLabel k})" s!"trans={expected}")
  else
    throw s!"case {a.name}: missing SameSig expectation"

def checkBundleLengthTheorem (theoremName : String) (bundles : List (List Nat)) : Bool :=
  match theoremName, bundles with
  | "bundleLength_append", [a, b] => (bundleAppendList a b).length == a.length + b.length
  | "bundleAppend_nil_right", [a] => bundleAppendList a [] == a
  | "bundleAppend_assoc", [a, b, c] => bundleAppendList a (bundleAppendList b c) == bundleAppendList (bundleAppendList a b) c
  | "bundleAppend_eq_right_iff_left_nil", [a, b] => (bundleAppendList a b == b) == (a == [])
  | "bundleAppend_eq_left_iff_right_nil", [a, b] => (bundleAppendList a b == a) == (b == [])
  | "bundleAppend_split_unique_fixed_length", [a, b, c, d] =>
      !((bundleAppendList a b == bundleAppendList c d) && a.length == c.length) || (a == c && b == d)
  | "bundleAppend_split_unique_fixed_suffix_length", [a, b, c, d] =>
      !((bundleAppendList a b == bundleAppendList c d) && b.length == d.length) || (a == c && b == d)
  | "bundleAppend_three_split_unique_fixed_lengths", [a, b, c, d, e, f] =>
      !((bundleAppendList a (bundleAppendList b c) == bundleAppendList d (bundleAppendList e f)) &&
          a.length == d.length && b.length == e.length) || (a == d && b == e && c == f)
  | _, _ => false

def bundleLengthArity (theoremName : String) : Except String Nat :=
  match theoremName with
  | "bundleLength_append" => pure 2
  | "bundleAppend_nil_right" => pure 1
  | "bundleAppend_assoc" => pure 3
  | "bundleAppend_eq_right_iff_left_nil" => pure 2
  | "bundleAppend_eq_left_iff_right_nil" => pure 2
  | "bundleAppend_split_unique_fixed_length" => pure 4
  | "bundleAppend_split_unique_fixed_suffix_length" => pure 4
  | "bundleAppend_three_split_unique_fixed_lengths" => pure 6
  | other => throw s!"unsupported bundle length theorem {other}"

def checkBundleLength (path : String) (a : Assertion) : Except String String := do
  let theoremName <- match fieldValue? a.fields "theorem" with
    | some t => pure (fieldAtom t)
    | none => throw s!"case {a.name}: missing theorem field"
  let expected <- expectBool a ["conclusion_holds"]
  let events <- decodeAllEvents a.input
  let arity <- bundleLengthArity theoremName
  let (bundles, rest) <- parseNBundlesFor .bundleLength arity events
  requireNoRest rest
  boolExpected (checkBundleLengthTheorem theoremName bundles) expected
  pure (passLine path .bundleLength a s!"{bundles.map natListLabel}" s!"theorem={theoremName}")

def checkBundleMembershipTheorem (theoremName : String) (probe? : Option Nat) (bundles : List (List Nat)) : Bool :=
  match theoremName, probe?, bundles with
  | "inBundle_nil_elim", some p, [a] => !(bundleContains p a)
  | "inBundle_cons_self", some p, [a] => match a with | x :: _ => x == p && bundleContains p a | [] => false
  | "inBundle_singleton_iff", some p, [a] => a.length == 1 && (bundleContains p a == (some p == a.head?))
  | "inBundle_bundleAppend_iff", some p, [a, b] => bundleContains p (bundleAppendList a b) == (bundleContains p a || bundleContains p b)
  | "inBundle_bundleAppend_left_of_not_right", some p, [a, b] =>
      !(bundleContains p (bundleAppendList a b) && !bundleContains p b) || bundleContains p a
  | "inBundle_bundleAppend_right_of_not_left", some p, [a, b] =>
      !(bundleContains p (bundleAppendList a b) && !bundleContains p a) || bundleContains p b
  | "inBundle_bundleAppend_three_iff", some p, [a, b, c] =>
      bundleContains p (bundleAppendList a (bundleAppendList b c)) == (bundleContains p a || bundleContains p b || bundleContains p c)
  | "inBundle_bundleAppend_four_iff", some p, [a, b, c, d] =>
      bundleContains p (bundleAppendList a (bundleAppendList b (bundleAppendList c d))) ==
        (bundleContains p a || bundleContains p b || bundleContains p c || bundleContains p d)
  | "inBundle_member_split_iff", some p, [a] => bundleContains p a == bundleContains p a
  | "bundleAppend_cancellation", none, [a, b, c, d] =>
      (!(bundleAppendList a b == bundleAppendList a c) || b == c) &&
        (!(bundleAppendList b d == bundleAppendList c d) || b == c)
  | "bundleAppend_cons_result_iff", none, [a, b, c] =>
      c.length > 0 &&
        (!(bundleAppendList a b == c) ||
          match a with
          | [] => b == c
          | _ :: tail => bundleAppendList tail b == c.drop 1)
  | "bundleAppend_empty_result_inversion", none, [a, b] =>
      !((bundleAppendList a b).length == 0) || (a == [] && b == [])
  | _, _, _ => false

def bundleMembershipShape (theoremName : String) : Except String (Bool × Nat) :=
  match theoremName with
  | "inBundle_nil_elim" => pure (true, 1)
  | "inBundle_cons_self" => pure (true, 1)
  | "inBundle_singleton_iff" => pure (true, 1)
  | "inBundle_bundleAppend_iff" => pure (true, 2)
  | "inBundle_bundleAppend_left_of_not_right" => pure (true, 2)
  | "inBundle_bundleAppend_right_of_not_left" => pure (true, 2)
  | "inBundle_bundleAppend_three_iff" => pure (true, 3)
  | "inBundle_bundleAppend_four_iff" => pure (true, 4)
  | "inBundle_member_split_iff" => pure (true, 1)
  | "bundleAppend_cancellation" => pure (false, 4)
  | "bundleAppend_cons_result_iff" => pure (false, 3)
  | "bundleAppend_empty_result_inversion" => pure (false, 2)
  | other => throw s!"unsupported bundle membership theorem {other}"

def checkBundleMembership (path : String) (a : Assertion) : Except String String := do
  let theoremName <- match fieldValue? a.fields "theorem" with
    | some t => pure (fieldAtom t)
    | none => throw s!"case {a.name}: missing theorem field"
  let expected <- expectBool a ["conclusion_holds"]
  let events <- decodeAllEvents a.input
  let (hasProbe, arity) <- bundleMembershipShape theoremName
  let (probe?, rest) <- if hasProbe then
      let (p, rest) <- parseNatFromEvents events
      pure (some p, rest)
    else
      pure (none, events)
  let (bundles, rest) <- parseNBundlesFor .bundleMembership arity rest
  requireNoRest rest
  boolExpected (checkBundleMembershipTheorem theoremName probe? bundles) expected
  pure (passLine path .bundleMembership a s!"probe={probe?} bundles={bundles.map natListLabel}" s!"theorem={theoremName}")

def checkUnary (path : String) (a : Assertion) : Except String String := do
  if let some value := fieldValue? a.fields "unary" then
    let expected := fieldAtom value == "yes"
    let decoded <- try
        let h <- match (← decodeExactlyEvents a.input 1) with
          | [event] => pure (parseBHistEvent event)
          | _ => throw "internal arity mismatch"
        if u : unaryHistoryBool h = true then
          let _proof : UnaryHistory h := unaryPositiveGroundOk h u
          pure (true, histLabel h)
        else
          pure (false, histLabel h)
      catch _ =>
        pure (false, a.input)
    boolExpected decoded.fst expected
    pure (passLine path .unary a decoded.snd s!"unary={if expected then "yes" else "no"}")
  else
    let expected <- expectBool a ["cont_unary"]
    let (h, k, r) <- decodeThreeBHists a.input
    let truth := unaryHistoryBool h && unaryHistoryBool k && r == appendHist h k && unaryHistoryBool r
    boolExpected truth expected
    pure (passLine path .unary a s!"({histLabel h},{histLabel k},{histLabel r})" s!"cont_unary={if expected then "yes" else "no"}")

def checkAsk (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["ask_holds"]
  let truth <- try
      let events <- decodeAllEvents a.input
      let (p, rest) <- parseNatFromEvents events
      let (h, rest) <- parseBHistFromEvents rest
      let (m, rest) <- parseBMarkFromEvents rest
      let (ev, rest) <- parseBMarkFromEvents rest
      requireNoRest rest
      let expectedMark := askExpected p h
      if hm : m = expectedMark ∧ ev = expectedMark then
        let _proof : Ask p h m ev := askPositiveGroundOk p h m ev hm.left hm.right
        pure true
      else
        let _proof : Not (Ask p h m ev) := askNegativeGroundOk p h m ev hm
        pure false
    catch _ =>
      pure false
  boolExpected truth expected
  pure (passLine path .ask a a.input s!"ask_holds={if expected then "yes" else "no"}")

def checkGap (path : String) (a : Assertion) : Except String String := do
  let events <- decodeAllEvents a.input
  let tag? := match events with
    | event :: rest =>
        if rawEventEq event [BMark.b0] then some (BMark.b0, rest)
        else if rawEventEq event [BMark.b1] then some (BMark.b1, rest)
        else none
    | [] => none
  match tag? with
  | some (BMark.b0, rest) =>
      let expected <- expectBool a ["ingap"]
      let truth <- try
          let (bound, rest) <- parseNatFromEvents rest
          let (bundle, rest) <- parseBundleFor .gap rest
          let (h, rest) <- parseBHistFromEvents rest
          let (s, rest) <- parseBHistFromEvents rest
          let (p, rest) <- parseBHistFromEvents rest
          requireNoRest rest
          pure (histDepth h <= bound && sigResult bundle h == s && s == p)
        catch _ =>
          pure false
      boolExpected truth expected
      pure (passLine path .gap a a.input s!"ingap={if expected then "yes" else "no"}")
  | some (BMark.b1, rest) =>
      let expected <- expectBool a ["comp"]
      let truth <- try
          let (_source, rest) <- parseBHistFromEvents rest
          let (_inter, rest) <- parseBHistFromEvents rest
          let (_final, rest) <- parseBHistFromEvents rest
          let ((first, second), rest) <- parseTwoBitsFromEvents rest
          requireNoRest rest
          pure (first && second)
        catch _ =>
          pure false
      boolExpected truth expected
      pure (passLine path .gap a a.input s!"comp={if expected then "yes" else "no"}")
  | none =>
      let expected <- expectBool a ["reject"]
      boolExpected true expected
      pure (passLine path .gap a a.input s!"reject={if expected then "yes" else "no"}")

def checkPackage (path : String) (a : Assertion) : Except String String := do
  let events <- decodeAllEvents a.input
  let (tag, rest) <- parseNatFromEvents events
  let truth <- try
      match tag with
      | 0 =>
          let (_bundle, rest) <- parseBundleFor .package rest
          let (s, rest) <- parseBHistFromEvents rest
          let (p, rest) <- parseBHistFromEvents rest
          requireNoRest rest
          pure (tokIntroBool s p)
      | 1 =>
          let (_bundle, rest) <- parseBundleFor .package rest
          let (s, rest) <- parseBHistFromEvents rest
          let (t, rest) <- parseBHistFromEvents rest
          let (p, rest) <- parseBHistFromEvents rest
          let (q, rest) <- parseBHistFromEvents rest
          requireNoRest rest
          pure (psameBool s t p q)
      | 2 =>
          let (_bundle, rest) <- parseBundleFor .package rest
          let (s, rest) <- parseBHistFromEvents rest
          let (t, rest) <- parseBHistFromEvents rest
          let (p, rest) <- parseBHistFromEvents rest
          let (q, rest) <- parseBHistFromEvents rest
          let ((claimedP, claimedH), rest) <- parseTwoBitsFromEvents rest
          requireNoRest rest
          let introduced := tokIntroBool s p && tokIntroBool t q
          let actualH := introduced && s == t
          let actualP := introduced && psameBool s t p q
          pure (introduced && claimedP == actualP && claimedH == actualH)
      | 3 =>
          let (_bundle, rest) <- parseBundleFor .package rest
          let (h, rest) <- parseBHistFromEvents rest
          let (k, rest) <- parseBHistFromEvents rest
          let (l, rest) <- parseBHistFromEvents rest
          let (p, rest) <- parseBHistFromEvents rest
          let (q, rest) <- parseBHistFromEvents rest
          let (r, rest) <- parseBHistFromEvents rest
          requireNoRest rest
          pure (psameBool h k p q && psameBool k l q r && psameBool h l p r)
      | _ => pure false
    catch _ =>
      pure false
  let (key, expected) <-
    if let some v := fieldValue? a.fields "token" then pure ("token", fieldAtom v == "yes")
    else if let some v := fieldValue? a.fields "psame" then pure ("psame", fieldAtom v == "yes")
    else if let some v := fieldValue? a.fields "classification" then pure ("classification", fieldAtom v == "yes")
    else if let some v := fieldValue? a.fields "chain" then pure ("chain", fieldAtom v == "yes")
    else if let some v := fieldValue? a.fields "reject" then pure ("reject", !(fieldAtom v == "yes"))
    else throw s!"case {a.name}: missing package expectation"
  boolExpected truth expected
  pure (passLine path .package a a.input s!"{key}={if expected then "yes" else "no"}")

def carrierBound (bound : Nat) (h : BHist) : Bool := histDepth h <= bound
def equivDepth (h k : BHist) : Bool := histDepth h == histDepth k

def bitMatches (bit : Bool) (truth : Bool) : Bool := bit == truth

def checkNameCertTruth (events : List RawEvent) : Except String Bool := do
  let (tag, rest) <- parseNatFromEvents events
  match tag with
  | 0 =>
      let (bound, rest) <- parseNatFromEvents rest
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      let (r, rest) <- parseBHistFromEvents rest
      let event <- match rest with | e :: tail => pure (e, tail) | [] => throw "missing relation bits"
      let rel := event.fst.map (· == BMark.b1)
      requireNoRest event.snd
      match rel with
      | [hkBit, krBit, sourceBit] =>
          let hk := equivDepth h k
          let kr := equivDepth k r
          let source := carrierBound bound h
          pure (bitMatches hkBit hk && bitMatches krBit kr && bitMatches sourceBit source &&
            (!source || equivDepth h h) && (!hk || equivDepth k h) &&
            (!(hk && kr) || equivDepth h r) && (!(hk && source) || carrierBound bound k))
      | _ => pure false
  | 1 =>
      let (bound, rest) <- parseNatFromEvents rest
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      let (r, rest) <- parseBHistFromEvents rest
      let event <- match rest with | e :: tail => pure (e, tail) | [] => throw "missing relation bits"
      let rel := event.fst.map (· == BMark.b1)
      requireNoRest event.snd
      match rel with
      | [hkBit, krBit, sourceBit] =>
          let hk := equivDepth h k
          let kr := equivDepth k r
          let source := carrierBound bound h
          pure (bitMatches hkBit hk && bitMatches krBit kr && bitMatches sourceBit source &&
            (!source || (carrierBound bound h && carrierBound bound h)) &&
            (!(hk && source) || carrierBound bound k) &&
            (!(hk && kr && source) || carrierBound bound r))
      | _ => pure false
  | 2 =>
      let (_thread, rest) <- parseNatFromEvents rest
      let (bound, rest) <- parseNatFromEvents rest
      requireNoRest rest
      pure (carrierBound bound BHist.Empty)
  | 3 =>
      let (source, rest) <- parseBHistFromEvents rest
      let (target, rest) <- parseBHistFromEvents rest
      let event <- match rest with | e :: tail => pure (e, tail) | [] => throw "missing stable bits"
      let rel := event.fst.map (· == BMark.b1)
      requireNoRest event.snd
      match rel with
      | [sameBit, ledgerBit] =>
          let same := equivDepth source target
          pure (bitMatches sameBit same && ledgerBit && (!same || equivDepth source target))
      | _ => pure false
  | 4 =>
      let (source, rest) <- parseBHistFromEvents rest
      let (target, rest) <- parseBHistFromEvents rest
      let event <- match rest with | e :: tail => pure (e, tail) | [] => throw "missing composition bits"
      let rel := event.fst.map (· == BMark.b1)
      requireNoRest event.snd
      match rel with
      | [sameBit, leftLedger, rightLedger] =>
          let same := equivDepth source target
          pure (bitMatches sameBit same && leftLedger && rightLedger && (!same || equivDepth source target))
      | _ => pure false
  | 5 =>
      let (left, rest) <- parseNatFromEvents rest
      let (right, rest) <- parseNatFromEvents rest
      requireNoRest rest
      pure (left < 5 && right < 5 && left != right)
  | _ => pure false

def checkNameCert (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["name_cert"]
  let truth <- try checkNameCertTruth (← decodeAllEvents a.input) catch _ => pure false
  boolExpected truth expected
  pure (passLine path .nameCert a a.input s!"name_cert={if expected then "yes" else "no"}")

def checkSettledHistory (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 =>
      let (h, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h == 1)
  | 1 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h == 1 && histDepth k == 1 && h != k)
  | 2 =>
      let (_h, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure true
  | 3 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (k == BHist.e0 h)
  | 4 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h <= 1 && histDepth k <= 1)
  | _ => pure false

def checkSettledExtCont (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (mHist, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      match mHist with
      | BHist.e0 BHist.Empty => pure (extResult a BMark.b0 == c && extResult a BMark.b0 == d && c == d)
      | BHist.e1 BHist.Empty => pure (extResult a BMark.b1 == c && extResult a BMark.b1 == d && c == d)
      | _ => pure false
  | 1 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (appendHist a b == c && appendHist a b == d && c == d)
  | 2 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (appendHist BHist.Empty a == b && a == b)
  | 3 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (appendHist a BHist.Empty == b && a == b)
  | 4 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      let (e, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let ab := appendHist a b
      let bc := appendHist b c
      pure (appendHist ab c == d && appendHist a bc == e && d == e)
  | _ => pure false

def checkSettledSignature (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  let (bundle, rest) <- parseBundleFor .settled rest
  match subcase with
  | 0 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (s, rest) <- parseBHistFromEvents rest
      let (t, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let computed := sigResult bundle h
      pure (!((computed == s) && (computed == t)) || s == t)
  | 1 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (!sameSigFixture bundle h k || sameSigFixture bundle k h)
  | 2 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      let (l, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let hk := sameSigFixture bundle h k
      let kl := sameSigFixture bundle k l
      let hl := sameSigFixture bundle h l
      pure (!(hk && kl) || hl)
  | _ => pure false

def checkSettledPackageGap (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 => checkGap pathPlaceholder { name := "settled-ingap", input := "", fields := [] } *> pure false
  | 1 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (!(a == b && a == c && b == d) || c == d)
  | 2 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (a == b)
  | _ => pure false
where
  pathPlaceholder := ""

def parseInGapTail (rest : List RawEvent) : Except String Bool := do
  let (bound, rest) <- parseNatFromEvents rest
  let (bundle, rest) <- parseBundleFor .gap rest
  let (h, rest) <- parseBHistFromEvents rest
  let (s, rest) <- parseBHistFromEvents rest
  let (p, rest) <- parseBHistFromEvents rest
  requireNoRest rest
  pure (histDepth h <= bound && sigResult bundle h == s && s == p)

def checkSettledGlobalize (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 =>
      let (bound, rest) <- parseNatFromEvents rest
      let (bundle, rest) <- parseBundleFor .settled rest
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      let (p, rest) <- parseBHistFromEvents rest
      let (q, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let sigH := sigResult bundle h
      let sigK := sigResult bundle k
      pure (histDepth h <= bound && histDepth k <= bound && sigH == p && sigK == q && ((p == q) == (sigH == sigK)))
  | 1 =>
      let (bound, rest) <- parseNatFromEvents rest
      let (bundle, rest) <- parseBundleFor .settled rest
      let (h, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h <= bound && sigResult bundle h == sigResult bundle h)
  | _ => pure false

def checkSettledComposite (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  if subcase != 0 then pure false else
  let (_source, rest) <- parseBHistFromEvents rest
  let (_inter, rest) <- parseBHistFromEvents rest
  let (_final, rest) <- parseBHistFromEvents rest
  let ((first, second), rest) <- parseTwoBitsFromEvents rest
  requireNoRest rest
  pure (first && second)

def checkSettledNameCert (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  if subcase == 3 then
    requireNoRest rest
    pure true
  else
    let (h, rest) <- parseBHistFromEvents rest
    let (k, rest) <- parseBHistFromEvents rest
    requireNoRest rest
    match subcase with
    | 0 => pure (unaryHistoryBool h && unaryHistoryBool k && h == k)
    | 1 => pure (unaryHistoryBool h && h == k && unaryHistoryBool k)
    | 2 => pure (h == k)
    | _ => pure false

def checkSettledDescent (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  if subcase != 0 then pure false else
  let (_a, rest) <- parseBHistFromEvents rest
  let (_b, rest) <- parseBHistFromEvents rest
  requireNoRest rest
  pure true

def checkSettledBundle (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  if subcase != 0 then pure false else
  let (_bundle, rest) <- parseBundleFor .settled rest
  requireNoRest rest
  pure true

def checkSettledTruth (events : List RawEvent) : Except String Bool := do
  let (family, rest) <- parseNatFromEvents events
  let (subcase, rest) <- parseNatFromEvents rest
  match family with
  | 0 => checkSettledHistory subcase rest
  | 1 => checkSettledExtCont subcase rest
  | 2 => checkSettledSignature subcase rest
  | 3 =>
      if subcase == 0 then parseInGapTail rest else checkSettledPackageGap subcase rest
  | 4 => checkSettledGlobalize subcase rest
  | 5 => checkSettledComposite subcase rest
  | 6 => checkSettledNameCert subcase rest
  | 7 => checkSettledDescent subcase rest
  | 8 => checkSettledBundle subcase rest
  | _ => pure false

def checkSettled (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["settled"]
  let truth <- try checkSettledTruth (← decodeAllEvents a.input) catch _ => pure false
  boolExpected truth expected
  pure (passLine path .settled a a.input s!"settled={if expected then "yes" else "no"}")

partial def hasDuplicateCase : List String -> Bool
  | [] => false
  | name :: rest => rest.contains name || hasDuplicateCase rest

def checkManifest (path : String) (manifest : Manifest) : Except String (List String) := do
  let family <- familyOfPath path
  if manifest.productions != 0 then
    throw s!"{family.name} manifest must have PRODUCTIONS 0, got {manifest.productions}"
  if manifest.assertions.length != manifest.assertionsDeclared then
    throw s!"assertion count mismatch: declared {manifest.assertionsDeclared}, parsed {manifest.assertions.length}"
  if hasDuplicateCase (manifest.assertions.map (·.name)) then
    throw "duplicate assertion case name"
  match family with
  | .markRefl => manifest.assertions.mapM (checkMarkRefl path)
  | .markSymm => manifest.assertions.mapM (checkMarkSymm path)
  | .markTrans => manifest.assertions.mapM (checkMarkTrans path)
  | .markNoConfusion => manifest.assertions.mapM (checkMarkNoConfusion path)
  | .histRefl => manifest.assertions.mapM (checkHistRefl path)
  | .histSymm => manifest.assertions.mapM (checkHistSymm path)
  | .histTrans => manifest.assertions.mapM (checkHistTrans path)
  | .histEmpty => manifest.assertions.mapM (checkHistEmpty path)
  | .histDistinct => manifest.assertions.mapM (checkHistDistinct path)
  | .ext => manifest.assertions.mapM (checkExtStep path)
  | .cont => manifest.assertions.mapM (checkContLike .cont "cont_holds" path)
  | .sigRel => manifest.assertions.mapM (checkSigRel path)
  | .sameSig => manifest.assertions.mapM (checkSameSig path)
  | .bundleLength => manifest.assertions.mapM (checkBundleLength path)
  | .bundleMembership => manifest.assertions.mapM (checkBundleMembership path)
  | .unary => manifest.assertions.mapM (checkUnary path)
  | .ask => manifest.assertions.mapM (checkAsk path)
  | .externalBinary => manifest.assertions.mapM (checkContLike .externalBinary "external_append_holds" path)
  | .gap => manifest.assertions.mapM (checkGap path)
  | .package => manifest.assertions.mapM (checkPackage path)
  | .nameCert => manifest.assertions.mapM (checkNameCert path)
  | .settled => manifest.assertions.mapM (checkSettled path)

def registeredManifests : List String :=
  registeredManifestSpecs.map (fun spec => "../rule110/" ++ spec.fst)

def usage : String :=
  "usage: cd lean4 && lake exe rule110-cross-check [manifest.enum.ct]..."

def runOne (path : String) : IO UInt32 := do
  let content <- IO.FS.readFile path
  match parseManifest content >>= checkManifest path with
  | Except.ok lines =>
      for line in lines do
        IO.println line
      pure 0
  | Except.error e =>
      IO.eprintln s!"FAIL path={path}: {e}"
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
