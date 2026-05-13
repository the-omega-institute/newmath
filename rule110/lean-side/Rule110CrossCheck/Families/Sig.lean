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
import Rule110CrossCheck.Decoder
import Rule110CrossCheck.Reporting

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

theorem sigEmptyGroundOk (h r : BHist) (hr : r = BHist.Empty) :
    SigRel (ProbeBundle.Bnil : ProbeBundle Nat) h r := by
  cases hr
  exact SigRel.empty h


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

end BEDC.Rule110CrossCheck
