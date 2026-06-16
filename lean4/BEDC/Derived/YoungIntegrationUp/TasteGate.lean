import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungIntegrationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungIntegrationUp : Type where
  | mk (F G A B W V D R E H C P N : BHist) : YoungIntegrationUp
  deriving DecidableEq

def youngIntegrationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngIntegrationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngIntegrationEncodeBHist h

def youngIntegrationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngIntegrationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngIntegrationDecodeBHist tail)

private theorem youngIntegrationDecodeEncodeBHist :
    ∀ h : BHist, youngIntegrationDecodeBHist (youngIntegrationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngIntegrationToEventFlow : YoungIntegrationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | YoungIntegrationUp.mk F G A B W V D R E H C P N =>
      [youngIntegrationEncodeBHist F,
        youngIntegrationEncodeBHist G,
        youngIntegrationEncodeBHist A,
        youngIntegrationEncodeBHist B,
        youngIntegrationEncodeBHist W,
        youngIntegrationEncodeBHist V,
        youngIntegrationEncodeBHist D,
        youngIntegrationEncodeBHist R,
        youngIntegrationEncodeBHist E,
        youngIntegrationEncodeBHist H,
        youngIntegrationEncodeBHist C,
        youngIntegrationEncodeBHist P,
        youngIntegrationEncodeBHist N]

private def youngIntegrationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => youngIntegrationEventAtDefault index rest

def youngIntegrationFromEventFlow (ef : EventFlow) : Option YoungIntegrationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (YoungIntegrationUp.mk
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 0 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 1 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 2 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 3 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 4 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 5 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 6 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 7 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 8 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 9 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 10 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 11 ef))
      (youngIntegrationDecodeBHist (youngIntegrationEventAtDefault 12 ef)))

private theorem youngIntegrationRoundTrip :
    ∀ x : YoungIntegrationUp,
      youngIntegrationFromEventFlow (youngIntegrationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G A B W V D R E H C P N =>
      change
        some
          (YoungIntegrationUp.mk
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist F))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist G))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist A))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist B))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist W))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist V))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist D))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist R))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist E))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist H))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist C))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist P))
            (youngIntegrationDecodeBHist (youngIntegrationEncodeBHist N))) =
          some (YoungIntegrationUp.mk F G A B W V D R E H C P N)
      rw [youngIntegrationDecodeEncodeBHist F,
        youngIntegrationDecodeEncodeBHist G,
        youngIntegrationDecodeEncodeBHist A,
        youngIntegrationDecodeEncodeBHist B,
        youngIntegrationDecodeEncodeBHist W,
        youngIntegrationDecodeEncodeBHist V,
        youngIntegrationDecodeEncodeBHist D,
        youngIntegrationDecodeEncodeBHist R,
        youngIntegrationDecodeEncodeBHist E,
        youngIntegrationDecodeEncodeBHist H,
        youngIntegrationDecodeEncodeBHist C,
        youngIntegrationDecodeEncodeBHist P,
        youngIntegrationDecodeEncodeBHist N]

private theorem youngIntegrationToEventFlow_injective {x y : YoungIntegrationUp} :
    youngIntegrationToEventFlow x = youngIntegrationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngIntegrationFromEventFlow (youngIntegrationToEventFlow x) =
        youngIntegrationFromEventFlow (youngIntegrationToEventFlow y) :=
    congrArg youngIntegrationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (youngIntegrationRoundTrip x).symm (Eq.trans hread (youngIntegrationRoundTrip y)))

private def youngIntegrationFields : YoungIntegrationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungIntegrationUp.mk F G A B W V D R E H C P N => [F, G, A, B, W, V, D, R, E, H, C, P, N]

private theorem youngIntegrationFieldFaithful :
    ∀ x y : YoungIntegrationUp, youngIntegrationFields x = youngIntegrationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 G1 A1 B1 W1 V1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 G2 A2 B2 W2 V2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance youngIntegrationBHistCarrier : BHistCarrier YoungIntegrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngIntegrationToEventFlow
  fromEventFlow := youngIntegrationFromEventFlow

instance youngIntegrationChapterTasteGate : ChapterTasteGate YoungIntegrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngIntegrationFromEventFlow (youngIntegrationToEventFlow x) = some x
    exact youngIntegrationRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (youngIntegrationToEventFlow_injective heq)

instance youngIntegrationFieldFaithfulInstance : FieldFaithful YoungIntegrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := youngIntegrationFields
  field_faithful := youngIntegrationFieldFaithful

instance youngIntegrationNontrivial : Nontrivial YoungIntegrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨YoungIntegrationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      YoungIntegrationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate YoungIntegrationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  youngIntegrationChapterTasteGate

theorem YoungIntegrationTasteGate_single_carrier_alignment :
    (∀ h : BHist, youngIntegrationDecodeBHist (youngIntegrationEncodeBHist h) = h) ∧
      (∀ x : YoungIntegrationUp,
        youngIntegrationFromEventFlow (youngIntegrationToEventFlow x) = some x) ∧
        (∀ x y : YoungIntegrationUp,
          youngIntegrationToEventFlow x = youngIntegrationToEventFlow y → x = y) ∧
          youngIntegrationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨youngIntegrationDecodeEncodeBHist,
      youngIntegrationRoundTrip,
      (fun _ _ heq => youngIntegrationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.YoungIntegrationUp
