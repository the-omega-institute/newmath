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

end BEDC.Rule110CrossCheck
