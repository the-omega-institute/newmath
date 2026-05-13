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

end BEDC.Rule110CrossCheck
