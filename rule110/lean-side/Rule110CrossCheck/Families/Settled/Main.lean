import Rule110CrossCheck.Families.Settled.PackageGlobal
import BEDC.GroundCompiler.ChannelEncoding

open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

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

end BEDC.Rule110CrossCheck
