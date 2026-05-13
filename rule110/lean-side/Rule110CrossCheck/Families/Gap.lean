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

end BEDC.Rule110CrossCheck
