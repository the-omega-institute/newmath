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

theorem msameReflGroundOk (m n : BMark) (h : m = n) : msame m n := by
  cases h
  exact msame_refl m


def checkMarkRefl (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_reflexive", "expect_reflexive"]) != "yes" then
    throw s!"case {a.name}: reflexive expectation must be yes"
  let (m, n) <- decodeTwoBMarks a.input
  if h : m = n then
    let _proof : msame m n := msameReflGroundOk m n h
    pure (passLine path .markRefl a s!"({markLabel m},{markLabel n})")
  else
    throw s!"case {a.name}: decoded ({markLabel m},{markLabel n}); expected reflexive pair"

def checkMarkSymm (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["conclusion_holds"]
  let (m, n) <- decodeTwoBMarks a.input
  let trivial := m == n
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected symm expectation {atom}"
  if h : m = n then
    let _proof : msame n m := msame_symm (msameReflGroundOk m n h)
    pure (passLine path .markSymm a s!"({markLabel m},{markLabel n})" s!"conclusion_holds={expected}")
  else
    pure (passLine path .markSymm a s!"({markLabel m},{markLabel n})" s!"conclusion_holds={expected}")

def checkMarkTrans (path : String) (a : Assertion) : Except String String := do
  let expected <- expectAtom a ["holds"]
  let (m, n, o) <- decodeThreeBMarks a.input
  let trivial := m == n && n == o
  match expected with
  | "trivial" => boolExpected trivial true
  | "vacuous" => boolExpected trivial false
  | atom => throw s!"case {a.name}: unexpected trans expectation {atom}"
  pure (passLine path .markTrans a s!"({markLabel m},{markLabel n},{markLabel o})" s!"holds={expected}")

def checkMarkNoConfusion (path : String) (a : Assertion) : Except String String := do
  if (← expectAtom a ["expected_unequal"]) != "yes" then
    throw s!"case {a.name}: expected_unequal must be yes"
  let (m, n) <- decodeTwoBMarks a.input
  if m == n then
    throw s!"case {a.name}: decoded equal marks"
  else
    pure (passLine path .markNoConfusion a s!"({markLabel m},{markLabel n})" "expected_unequal=yes")

end BEDC.Rule110CrossCheck
