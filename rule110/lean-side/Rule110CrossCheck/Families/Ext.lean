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

end BEDC.Rule110CrossCheck
