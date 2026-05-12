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

theorem hsameReflGroundOk (h k : BHist) (same : h = k) : hsame h k := by
  cases same
  exact hsame_refl h


def checkHistRefl (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_reflexive", "expect_reflexive"]) != "yes" then
    throw s!"case {a.name}: reflexive expectation must be yes"
  let (h, k) <- decodeTwoBHists a.input
  if same : h = k then
    let _proof : hsame h k := hsameReflGroundOk h k same
    pure (passLine path .histRefl a s!"({histLabel h},{histLabel k})")
  else
    throw s!"case {a.name}: decoded non-reflexive pair"

def checkHistSymm (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["conclusion_holds"]
  let (h, k) <- decodeTwoBHists a.input
  let trivial := h == k
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected symm expectation {atom}"
  pure (passLine path .histSymm a s!"({histLabel h},{histLabel k})" s!"conclusion_holds={expected}")

def checkHistTrans (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["holds"]
  let (h, k, l) <- decodeThreeBHists a.input
  let trivial := h == k && k == l
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected trans expectation {atom}"
  pure (passLine path .histTrans a s!"({histLabel h},{histLabel k},{histLabel l})" s!"holds={expected}")

def checkHistEmpty (path : String) (a : Assertion) : Except String String := do
  let expected <- expectBool a ["empty_match"]
  let (h, k) <- decodeTwoBHists a.input
  boolExpected (h == BHist.Empty && k == BHist.Empty) expected
  pure (passLine path .histEmpty a s!"({histLabel h},{histLabel k})" s!"empty_match={if expected then "yes" else "no"}")

def checkHistDistinct (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_unequal"]) != "yes" then
    throw s!"case {a.name}: expected_unequal must be yes"
  let (h, k) <- decodeTwoBHists a.input
  if h == k then
    throw s!"case {a.name}: decoded equal histories"
  else
    pure (passLine path .histDistinct a s!"({histLabel h},{histLabel k})" "expected_unequal=yes")

end BEDC.Rule110CrossCheck
