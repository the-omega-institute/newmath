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

theorem askPositiveGroundOk (p : Nat) (h : BHist) (m ev : BMark)
    (hm : m = askExpected p h) (he : ev = askExpected p h) :
    Ask p h m ev := by
  exact And.intro hm he

theorem askNegativeGroundOk (p : Nat) (h : BHist) (m ev : BMark)
    (bad : Not (m = askExpected p h ∧ ev = askExpected p h)) :
    Not (Ask p h m ev) := by
  exact bad


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

end BEDC.Rule110CrossCheck
