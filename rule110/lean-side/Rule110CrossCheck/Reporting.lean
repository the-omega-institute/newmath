import Rule110CrossCheck.Parser
import Rule110CrossCheck.Registry

namespace BEDC.Rule110CrossCheck

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

def boolExpected (truth : Bool) (expected : Bool) : Except String Unit :=
  if truth == expected then pure () else throw s!"semantic mismatch: computed {truth}, expected {expected}"

def passLine (path : String) (family : Family) (a : Assertion) (decoded : String) (polarity : String := "") : String :=
  let pol := if polarity = "" then "" else s!" {polarity}"
  s!"PASS path={path} family={family.name} case={a.name} decoded={decoded}{pol} target={family.targetKey}"

end BEDC.Rule110CrossCheck
