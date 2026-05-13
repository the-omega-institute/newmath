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

end BEDC.Rule110CrossCheck
