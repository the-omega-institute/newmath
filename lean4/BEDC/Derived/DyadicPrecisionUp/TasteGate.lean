import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# DyadicPrecisionUp TasteGate carrier.
-/

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite precision schedule token with the seven BEDC rows visible to consumers. -/
inductive DyadicPrecisionUp : Type where
  | mk :
      (precision radius window transport provenance nameCert ledger : BHist) →
      DyadicPrecisionUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def dyadicPrecisionToEventFlow : DyadicPrecisionUp → EventFlow
  | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
      [[BMark.b0],
        encodeBHist precision,
        [BMark.b1, BMark.b0],
        encodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist nameCert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist ledger]

private def dyadicPrecisionFromEventFlow : EventFlow → Option DyadicPrecisionUp
  | _tag0 :: precision :: _tag1 :: radius :: _tag2 :: window ::
      _tag3 :: transport :: _tag4 :: provenance :: _tag5 :: nameCert ::
      _tag6 :: ledger :: [] =>
      some (DyadicPrecisionUp.mk (decodeBHist precision) (decodeBHist radius)
        (decodeBHist window) (decodeBHist transport) (decodeBHist provenance)
        (decodeBHist nameCert) (decodeBHist ledger))
  | _ => none

private theorem dyadicPrecision_round_trip :
    ∀ x : DyadicPrecisionUp,
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x := by
  intro x
  cases x with
  | mk precision radius window transport provenance nameCert ledger =>
      simp only [dyadicPrecisionToEventFlow, dyadicPrecisionFromEventFlow, decode_encode_bhist]

private theorem dyadicPrecisionToEventFlow_injective {x y : DyadicPrecisionUp} :
    dyadicPrecisionToEventFlow x = dyadicPrecisionToEventFlow y → x = y := by
  intro heq
  have hread :
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) =
        dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow y) :=
    congrArg dyadicPrecisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicPrecision_round_trip x).symm
      (Eq.trans hread (dyadicPrecision_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  toEventFlow := dyadicPrecisionToEventFlow
  fromEventFlow := dyadicPrecisionFromEventFlow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  round_trip := by
    intro x
    change dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x
    exact dyadicPrecision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicPrecisionToEventFlow_injective heq)

/-- Public gate object for the finite dyadic-precision schedule carrier. -/
def taste_gate : ChapterTasteGate DyadicPrecisionUp :=
  dyadicPrecisionChapterTasteGate

end BEDC.Derived.DyadicPrecisionUp
