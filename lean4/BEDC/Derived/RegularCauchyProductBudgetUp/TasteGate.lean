import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyProductBudgetUp : Type where
  | mk
      (sourceA sourceB windowA windowB dyadicA dyadicB product budget readback sealRow
        transport routes provenance name : BHist) :
      RegularCauchyProductBudgetUp
  deriving DecidableEq

private def regularCauchyProductBudgetUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyProductBudgetUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyProductBudgetUpEncodeBHist h

private def regularCauchyProductBudgetUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyProductBudgetUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyProductBudgetUpDecodeBHist tail)

private theorem regularCauchyProductBudgetUp_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyProductBudgetUpDecodeBHist
        (regularCauchyProductBudgetUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def regularCauchyProductBudgetUpToEventFlow :
    RegularCauchyProductBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyProductBudgetUp.mk sourceA sourceB windowA windowB dyadicA dyadicB
      product budget readback sealRow transport routes provenance name =>
      [[BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist sourceA,
        [BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist sourceB,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist windowA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist windowB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist dyadicA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist dyadicB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist product,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetUpEncodeBHist name]

private def regularCauchyProductBudgetUpDecodeRows :
    RawEvent → RawEvent → RawEvent → RawEvent → RawEvent → RawEvent → RawEvent →
      RawEvent → RawEvent → RawEvent → RawEvent → RawEvent → RawEvent → RawEvent →
        RegularCauchyProductBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | sourceA, sourceB, windowA, windowB, dyadicA, dyadicB, product, budget,
      readback, sealRow, transport, routes, provenance, name =>
      RegularCauchyProductBudgetUp.mk
        (regularCauchyProductBudgetUpDecodeBHist sourceA)
        (regularCauchyProductBudgetUpDecodeBHist sourceB)
        (regularCauchyProductBudgetUpDecodeBHist windowA)
        (regularCauchyProductBudgetUpDecodeBHist windowB)
        (regularCauchyProductBudgetUpDecodeBHist dyadicA)
        (regularCauchyProductBudgetUpDecodeBHist dyadicB)
        (regularCauchyProductBudgetUpDecodeBHist product)
        (regularCauchyProductBudgetUpDecodeBHist budget)
        (regularCauchyProductBudgetUpDecodeBHist readback)
        (regularCauchyProductBudgetUpDecodeBHist sealRow)
        (regularCauchyProductBudgetUpDecodeBHist transport)
        (regularCauchyProductBudgetUpDecodeBHist routes)
        (regularCauchyProductBudgetUpDecodeBHist provenance)
        (regularCauchyProductBudgetUpDecodeBHist name)

private def regularCauchyProductBudgetUpFromEventFlow :
    EventFlow → Option RegularCauchyProductBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, sourceA, _tag1, sourceB, _tag2, windowA, _tag3, windowB, _tag4,
      dyadicA, _tag5, dyadicB, _tag6, product, _tag7, budget, _tag8, readback,
      _tag9, sealRow, _tag10, transport, _tag11, routes, _tag12, provenance, _tag13,
      name] =>
      some
        (regularCauchyProductBudgetUpDecodeRows sourceA sourceB windowA windowB
          dyadicA dyadicB product budget readback sealRow transport routes provenance name)
  | _ => none

private theorem regularCauchyProductBudgetUp_round_trip :
    ∀ x : RegularCauchyProductBudgetUp,
      regularCauchyProductBudgetUpFromEventFlow
        (regularCauchyProductBudgetUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceA sourceB windowA windowB dyadicA dyadicB product budget readback sealRow
      transport routes provenance name =>
      change
        some
          (RegularCauchyProductBudgetUp.mk
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist sourceA))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist sourceB))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist windowA))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist windowB))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist dyadicA))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist dyadicB))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist product))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist budget))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist readback))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist sealRow))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist transport))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist routes))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist provenance))
            (regularCauchyProductBudgetUpDecodeBHist
              (regularCauchyProductBudgetUpEncodeBHist name))) =
          some
            (RegularCauchyProductBudgetUp.mk sourceA sourceB windowA windowB dyadicA
              dyadicB product budget readback sealRow transport routes provenance name)
      rw [regularCauchyProductBudgetUp_decode_encode_bhist sourceA,
        regularCauchyProductBudgetUp_decode_encode_bhist sourceB,
        regularCauchyProductBudgetUp_decode_encode_bhist windowA,
        regularCauchyProductBudgetUp_decode_encode_bhist windowB,
        regularCauchyProductBudgetUp_decode_encode_bhist dyadicA,
        regularCauchyProductBudgetUp_decode_encode_bhist dyadicB,
        regularCauchyProductBudgetUp_decode_encode_bhist product,
        regularCauchyProductBudgetUp_decode_encode_bhist budget,
        regularCauchyProductBudgetUp_decode_encode_bhist readback,
        regularCauchyProductBudgetUp_decode_encode_bhist sealRow,
        regularCauchyProductBudgetUp_decode_encode_bhist transport,
        regularCauchyProductBudgetUp_decode_encode_bhist routes,
        regularCauchyProductBudgetUp_decode_encode_bhist provenance,
        regularCauchyProductBudgetUp_decode_encode_bhist name]

private theorem regularCauchyProductBudgetUpToEventFlow_injective
    {x y : RegularCauchyProductBudgetUp} :
    regularCauchyProductBudgetUpToEventFlow x =
      regularCauchyProductBudgetUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyProductBudgetUpFromEventFlow
          (regularCauchyProductBudgetUpToEventFlow x) =
        regularCauchyProductBudgetUpFromEventFlow
          (regularCauchyProductBudgetUpToEventFlow y) :=
    congrArg regularCauchyProductBudgetUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyProductBudgetUp_round_trip x).symm
      (Eq.trans hread (regularCauchyProductBudgetUp_round_trip y)))

instance regularCauchyProductBudgetUpBHistCarrier :
    BHistCarrier RegularCauchyProductBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyProductBudgetUpToEventFlow
  fromEventFlow := regularCauchyProductBudgetUpFromEventFlow

instance regularCauchyProductBudgetUpChapterTasteGate :
    ChapterTasteGate RegularCauchyProductBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyProductBudgetUpFromEventFlow
        (regularCauchyProductBudgetUpToEventFlow x) = some x
    exact regularCauchyProductBudgetUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyProductBudgetUpToEventFlow_injective heq)

end BEDC.Derived.RegularCauchyProductBudgetUp
