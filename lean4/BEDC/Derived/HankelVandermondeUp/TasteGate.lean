import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# HankelVandermondeUp TasteGate carrier.
-/

namespace BEDC.Derived.HankelVandermondeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite Hankel-Vandermonde packet with the ten BEDC rows visible to consumers. -/
inductive HankelVandermondeUp : Type where
  | mk :
      (atom weight moment determinantLedger pairwiseDifference vandermondeSquare transportRow
        routeRow provenance cert : BHist) →
      HankelVandermondeUp
  deriving DecidableEq

def hankelVandermondeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hankelVandermondeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hankelVandermondeEncodeBHist h

private def hankelVandermondeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hankelVandermondeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hankelVandermondeDecodeBHist tail)

private theorem hankelVandermondeDecodeEncodeBHist :
    ∀ h : BHist, hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def hankelVandermondeToEventFlow : HankelVandermondeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HankelVandermondeUp.mk atom weight moment determinantLedger pairwiseDifference
      vandermondeSquare transportRow routeRow provenance cert =>
      [[BMark.b0],
        hankelVandermondeEncodeBHist atom,
        [BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist weight,
        [BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist moment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist determinantLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist pairwiseDifference,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist vandermondeSquare,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hankelVandermondeEncodeBHist routeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist cert]

private def hankelVandermondeFromEventFlow : EventFlow → Option HankelVandermondeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, atom, _tag1, weight, _tag2, moment, _tag3, determinantLedger, _tag4,
      pairwiseDifference, _tag5, vandermondeSquare, _tag6, transportRow, _tag7, routeRow,
      _tag8, provenance, _tag9, cert] =>
      some
        (HankelVandermondeUp.mk
          (hankelVandermondeDecodeBHist atom)
          (hankelVandermondeDecodeBHist weight)
          (hankelVandermondeDecodeBHist moment)
          (hankelVandermondeDecodeBHist determinantLedger)
          (hankelVandermondeDecodeBHist pairwiseDifference)
          (hankelVandermondeDecodeBHist vandermondeSquare)
          (hankelVandermondeDecodeBHist transportRow)
          (hankelVandermondeDecodeBHist routeRow)
          (hankelVandermondeDecodeBHist provenance)
          (hankelVandermondeDecodeBHist cert))
  | _ => none

private theorem hankelVandermonde_round_trip :
    ∀ x : HankelVandermondeUp,
      hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk atom weight moment determinantLedger pairwiseDifference vandermondeSquare transportRow
      routeRow provenance cert =>
      change
        some
          (HankelVandermondeUp.mk
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist atom))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist weight))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist moment))
            (hankelVandermondeDecodeBHist
              (hankelVandermondeEncodeBHist determinantLedger))
            (hankelVandermondeDecodeBHist
              (hankelVandermondeEncodeBHist pairwiseDifference))
            (hankelVandermondeDecodeBHist
              (hankelVandermondeEncodeBHist vandermondeSquare))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist transportRow))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist routeRow))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist provenance))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist cert))) =
          some
            (HankelVandermondeUp.mk atom weight moment determinantLedger pairwiseDifference
              vandermondeSquare transportRow routeRow provenance cert)
      rw [hankelVandermondeDecodeEncodeBHist atom,
        hankelVandermondeDecodeEncodeBHist weight,
        hankelVandermondeDecodeEncodeBHist moment,
        hankelVandermondeDecodeEncodeBHist determinantLedger,
        hankelVandermondeDecodeEncodeBHist pairwiseDifference,
        hankelVandermondeDecodeEncodeBHist vandermondeSquare,
        hankelVandermondeDecodeEncodeBHist transportRow,
        hankelVandermondeDecodeEncodeBHist routeRow,
        hankelVandermondeDecodeEncodeBHist provenance,
        hankelVandermondeDecodeEncodeBHist cert]

private theorem hankelVandermondeToEventFlow_injective {x y : HankelVandermondeUp} :
    hankelVandermondeToEventFlow x = hankelVandermondeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) =
        hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow y) :=
    congrArg hankelVandermondeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hankelVandermonde_round_trip x).symm
      (Eq.trans hread (hankelVandermonde_round_trip y)))

instance hankelVandermondeBHistCarrier : BHistCarrier HankelVandermondeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hankelVandermondeToEventFlow
  fromEventFlow := hankelVandermondeFromEventFlow

instance hankelVandermondeChapterTasteGate : ChapterTasteGate HankelVandermondeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) = some x
    exact hankelVandermonde_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hankelVandermondeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HankelVandermondeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hankelVandermondeChapterTasteGate

end BEDC.Derived.HankelVandermondeUp
