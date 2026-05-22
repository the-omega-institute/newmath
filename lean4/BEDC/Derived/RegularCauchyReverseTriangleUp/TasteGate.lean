import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyReverseTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyReverseTriangleUp : Type where
  | mk :
      (sourceLeft sourceRight sourceDiff absLeft absRight absDiff diffAbs comparison
        readback sealRow transport replay provenance localCert : BHist) →
        RegularCauchyReverseTriangleUp
  deriving DecidableEq

def regularCauchyReverseTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyReverseTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyReverseTriangleEncodeBHist h

def regularCauchyReverseTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyReverseTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyReverseTriangleDecodeBHist tail)

private theorem regularCauchyReverseTriangle_decode_encode :
    ∀ h : BHist,
      regularCauchyReverseTriangleDecodeBHist
          (regularCauchyReverseTriangleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyReverseTriangleFields :
    RegularCauchyReverseTriangleUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyReverseTriangleUp.mk sourceLeft sourceRight sourceDiff absLeft absRight
      absDiff diffAbs comparison readback sealRow transport replay provenance localCert =>
      [sourceLeft, sourceRight, sourceDiff, absLeft, absRight, absDiff, diffAbs,
        comparison, readback, sealRow, transport, replay, provenance, localCert]

def regularCauchyReverseTriangleToEventFlow :
    RegularCauchyReverseTriangleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyReverseTriangleFields x).map regularCauchyReverseTriangleEncodeBHist

def regularCauchyReverseTriangleFromEventFlow :
    EventFlow → Option RegularCauchyReverseTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | sourceLeft :: sourceRight :: sourceDiff :: absLeft :: absRight :: absDiff ::
      diffAbs :: comparison :: readback :: sealRow :: transport :: replay :: provenance ::
      localCert :: [] =>
      some
        (RegularCauchyReverseTriangleUp.mk
          (regularCauchyReverseTriangleDecodeBHist sourceLeft)
          (regularCauchyReverseTriangleDecodeBHist sourceRight)
          (regularCauchyReverseTriangleDecodeBHist sourceDiff)
          (regularCauchyReverseTriangleDecodeBHist absLeft)
          (regularCauchyReverseTriangleDecodeBHist absRight)
          (regularCauchyReverseTriangleDecodeBHist absDiff)
          (regularCauchyReverseTriangleDecodeBHist diffAbs)
          (regularCauchyReverseTriangleDecodeBHist comparison)
          (regularCauchyReverseTriangleDecodeBHist readback)
          (regularCauchyReverseTriangleDecodeBHist sealRow)
          (regularCauchyReverseTriangleDecodeBHist transport)
          (regularCauchyReverseTriangleDecodeBHist replay)
          (regularCauchyReverseTriangleDecodeBHist provenance)
          (regularCauchyReverseTriangleDecodeBHist localCert))
  | _ => none

private theorem regularCauchyReverseTriangle_round_trip :
    ∀ x : RegularCauchyReverseTriangleUp,
      regularCauchyReverseTriangleFromEventFlow
          (regularCauchyReverseTriangleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk sourceLeft sourceRight sourceDiff absLeft absRight absDiff diffAbs comparison
      readback sealRow transport replay provenance localCert =>
      simp only [regularCauchyReverseTriangleToEventFlow,
        regularCauchyReverseTriangleFields, regularCauchyReverseTriangleFromEventFlow,
        List.map_cons, List.map_nil, regularCauchyReverseTriangle_decode_encode]

private theorem regularCauchyReverseTriangleToEventFlow_injective
    {x y : RegularCauchyReverseTriangleUp} :
    regularCauchyReverseTriangleToEventFlow x =
        regularCauchyReverseTriangleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyReverseTriangleFromEventFlow
            (regularCauchyReverseTriangleToEventFlow x) :=
        (regularCauchyReverseTriangle_round_trip x).symm
      _ =
          regularCauchyReverseTriangleFromEventFlow
            (regularCauchyReverseTriangleToEventFlow y) :=
        congrArg regularCauchyReverseTriangleFromEventFlow hxy
      _ = some y := regularCauchyReverseTriangle_round_trip y
  exact Option.some.inj optionEq

instance regularCauchyReverseTriangleBHistCarrier :
    BHistCarrier RegularCauchyReverseTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyReverseTriangleToEventFlow
  fromEventFlow := regularCauchyReverseTriangleFromEventFlow

instance regularCauchyReverseTriangleChapterTasteGate :
    ChapterTasteGate RegularCauchyReverseTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyReverseTriangleFromEventFlow
        (regularCauchyReverseTriangleToEventFlow x) =
      some x
    exact regularCauchyReverseTriangle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyReverseTriangleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyReverseTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyReverseTriangleChapterTasteGate

end BEDC.Derived.RegularCauchyReverseTriangleUp
