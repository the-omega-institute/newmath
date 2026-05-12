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

theorem contPositiveGroundOk (h k r : BHist) (result : r = appendHist h k) :
    BEDC.FKernel.Cont.Cont h k r := by
  exact BEDC.FKernel.Cont.cont_intro result

theorem contNegativeGroundOk (h k r : BHist) (result : Not (r = appendHist h k)) :
    Not (BEDC.FKernel.Cont.Cont h k r) := by
  intro hc
  exact result (Iff.mp BEDC.FKernel.Cont.cont_iff_append hc)


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

end BEDC.Rule110CrossCheck
