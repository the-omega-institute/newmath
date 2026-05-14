import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRealRouteCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRealRouteCommitmentUp : Type where
  | mk :
      (precision budget window readback sealRow handoffRow transport route provenance nameCert : BHist) →
        FiniteRealRouteCommitmentUp
  deriving DecidableEq

def finiteRealRouteCommitmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRealRouteCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRealRouteCommitmentEncodeBHist h

def finiteRealRouteCommitmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRealRouteCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRealRouteCommitmentDecodeBHist tail)

private theorem finiteRealRouteCommitment_decode_encode_bhist :
    ∀ h : BHist,
      finiteRealRouteCommitmentDecodeBHist (finiteRealRouteCommitmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteRealRouteCommitmentToEventFlow : FiniteRealRouteCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealRouteCommitmentUp.mk precision budget window readback sealRow handoffRow transport route
      provenance nameCert =>
      [[BMark.b0],
        finiteRealRouteCommitmentEncodeBHist precision,
        [BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist handoffRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteRealRouteCommitmentEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteRealRouteCommitmentEncodeBHist nameCert]

private def finiteRealRouteCommitmentRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteRealRouteCommitmentRawAt n rest

private def finiteRealRouteCommitmentLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteRealRouteCommitmentLengthEq n rest

def finiteRealRouteCommitmentFromEventFlow :
    EventFlow → Option FiniteRealRouteCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteRealRouteCommitmentLengthEq 20 flow with
      | true =>
          some
            (FiniteRealRouteCommitmentUp.mk
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 1 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 3 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 5 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 7 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 9 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 11 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 13 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 15 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 17 flow))
              (finiteRealRouteCommitmentDecodeBHist
                (finiteRealRouteCommitmentRawAt 19 flow)))
      | false => none

private theorem finiteRealRouteCommitment_round_trip :
    ∀ x : FiniteRealRouteCommitmentUp,
      finiteRealRouteCommitmentFromEventFlow (finiteRealRouteCommitmentToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision budget window readback sealRow handoffRow transport route provenance nameCert =>
      change
        some
          (FiniteRealRouteCommitmentUp.mk
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist precision))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist budget))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist window))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist readback))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist sealRow))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist handoffRow))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist transport))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist route))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist provenance))
            (finiteRealRouteCommitmentDecodeBHist
              (finiteRealRouteCommitmentEncodeBHist nameCert))) =
          some
            (FiniteRealRouteCommitmentUp.mk precision budget window readback sealRow handoffRow
              transport route provenance nameCert)
      rw [finiteRealRouteCommitment_decode_encode_bhist precision,
        finiteRealRouteCommitment_decode_encode_bhist budget,
        finiteRealRouteCommitment_decode_encode_bhist window,
        finiteRealRouteCommitment_decode_encode_bhist readback,
        finiteRealRouteCommitment_decode_encode_bhist sealRow,
        finiteRealRouteCommitment_decode_encode_bhist handoffRow,
        finiteRealRouteCommitment_decode_encode_bhist transport,
        finiteRealRouteCommitment_decode_encode_bhist route,
        finiteRealRouteCommitment_decode_encode_bhist provenance,
        finiteRealRouteCommitment_decode_encode_bhist nameCert]

private theorem finiteRealRouteCommitmentToEventFlow_injective
    {x y : FiniteRealRouteCommitmentUp} :
    finiteRealRouteCommitmentToEventFlow x = finiteRealRouteCommitmentToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRealRouteCommitmentFromEventFlow (finiteRealRouteCommitmentToEventFlow x) =
        finiteRealRouteCommitmentFromEventFlow (finiteRealRouteCommitmentToEventFlow y) :=
    congrArg finiteRealRouteCommitmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteRealRouteCommitment_round_trip x).symm
      (Eq.trans hread (finiteRealRouteCommitment_round_trip y)))

instance finiteRealRouteCommitmentBHistCarrier :
    BHistCarrier FiniteRealRouteCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRealRouteCommitmentToEventFlow
  fromEventFlow := finiteRealRouteCommitmentFromEventFlow

instance finiteRealRouteCommitmentChapterTasteGate :
    ChapterTasteGate FiniteRealRouteCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteRealRouteCommitmentFromEventFlow
        (finiteRealRouteCommitmentToEventFlow x) = some x
    exact finiteRealRouteCommitment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteRealRouteCommitmentToEventFlow_injective heq)

instance finiteRealRouteCommitmentFieldFaithful :
    FieldFaithful FiniteRealRouteCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteRealRouteCommitmentUp.mk precision budget window readback sealRow handoffRow transport
        route provenance nameCert =>
        [precision, budget, window, readback, sealRow, handoffRow, transport, route, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk precision1 budget1 window1 readback1 seal1 handoff1 transport1 route1 provenance1
        nameCert1 =>
        cases y with
        | mk precision2 budget2 window2 readback2 seal2 handoff2 transport2 route2 provenance2
            nameCert2 =>
            cases h
            rfl

instance finiteRealRouteCommitmentNontrivial :
    Nontrivial FiniteRealRouteCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteRealRouteCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteRealRouteCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteRealRouteCommitmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRealRouteCommitmentChapterTasteGate

theorem FiniteRealRouteCommitmentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteRealRouteCommitmentDecodeBHist (finiteRealRouteCommitmentEncodeBHist h) = h) ∧
      (∀ x : FiniteRealRouteCommitmentUp,
        finiteRealRouteCommitmentFromEventFlow
          (finiteRealRouteCommitmentToEventFlow x) = some x) ∧
        (∀ x y : FiniteRealRouteCommitmentUp,
          finiteRealRouteCommitmentToEventFlow x =
            finiteRealRouteCommitmentToEventFlow y → x = y) ∧
          finiteRealRouteCommitmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteRealRouteCommitment_decode_encode_bhist,
      finiteRealRouteCommitment_round_trip,
      by
        intro x y heq
        exact finiteRealRouteCommitmentToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FiniteRealRouteCommitmentUp
