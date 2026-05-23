import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMinimumUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMinimumUp : Type where
  | mk (X Y T L D A B W H C P N : BHist) : RegularCauchyMinimumUp
  deriving DecidableEq

def regularCauchyMinimumEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMinimumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMinimumEncodeBHist h

def regularCauchyMinimumDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMinimumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMinimumDecodeBHist tail)

private theorem regularCauchyMinimum_decode_encode_bhist :
    forall h : BHist, regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMinimumFields : RegularCauchyMinimumUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMinimumUp.mk X Y T L D A B W H C P N =>
      [X, Y, T, L, D, A, B, W, H, C, P, N]

def regularCauchyMinimumToEventFlow : RegularCauchyMinimumUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyMinimumFields x).map regularCauchyMinimumEncodeBHist

private def regularCauchyMinimumEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMinimumEventAt index rest

def regularCauchyMinimumFromEventFlow
    (ef : EventFlow) : Option RegularCauchyMinimumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMinimumUp.mk
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 0 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 1 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 2 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 3 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 4 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 5 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 6 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 7 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 8 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 9 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 10 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAt 11 ef)))

private theorem regularCauchyMinimum_round_trip
    (x : RegularCauchyMinimumUp) :
    regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y T L D A B W H C P N =>
      change
        some
          (RegularCauchyMinimumUp.mk
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist X))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist Y))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist T))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist L))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist D))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist A))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist B))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist W))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist H))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist C))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist P))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist N))) =
          some (RegularCauchyMinimumUp.mk X Y T L D A B W H C P N)
      rw [regularCauchyMinimum_decode_encode_bhist X,
        regularCauchyMinimum_decode_encode_bhist Y,
        regularCauchyMinimum_decode_encode_bhist T,
        regularCauchyMinimum_decode_encode_bhist L,
        regularCauchyMinimum_decode_encode_bhist D,
        regularCauchyMinimum_decode_encode_bhist A,
        regularCauchyMinimum_decode_encode_bhist B,
        regularCauchyMinimum_decode_encode_bhist W,
        regularCauchyMinimum_decode_encode_bhist H,
        regularCauchyMinimum_decode_encode_bhist C,
        regularCauchyMinimum_decode_encode_bhist P,
        regularCauchyMinimum_decode_encode_bhist N]

private theorem regularCauchyMinimumToEventFlow_injective
    {x y : RegularCauchyMinimumUp} :
    regularCauchyMinimumToEventFlow x = regularCauchyMinimumToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) =
        regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow y) :=
    congrArg regularCauchyMinimumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyMinimum_round_trip x).symm
      (Eq.trans hread (regularCauchyMinimum_round_trip y)))

private theorem regularCauchyMinimum_fields_faithful :
    forall x y : RegularCauchyMinimumUp,
      regularCauchyMinimumFields x = regularCauchyMinimumFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 T1 L1 D1 A1 B1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 T2 L2 D2 A2 B2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyMinimumBHistCarrier :
    BHistCarrier RegularCauchyMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMinimumToEventFlow
  fromEventFlow := regularCauchyMinimumFromEventFlow

instance regularCauchyMinimumChapterTasteGate :
    ChapterTasteGate RegularCauchyMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) = some x
    exact regularCauchyMinimum_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMinimumToEventFlow_injective heq)

instance regularCauchyMinimumFieldFaithful :
    FieldFaithful RegularCauchyMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyMinimumFields
  field_faithful := regularCauchyMinimum_fields_faithful

instance regularCauchyMinimumNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyMinimumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyMinimumUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyMinimumTasteGate_single_carrier_alignment :
    (forall h : BHist,
        regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist h) = h) ∧
      (forall x : RegularCauchyMinimumUp,
        regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) = some x) ∧
      (forall x y : RegularCauchyMinimumUp,
        regularCauchyMinimumToEventFlow x = regularCauchyMinimumToEventFlow y -> x = y) ∧
      regularCauchyMinimumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨regularCauchyMinimum_decode_encode_bhist,
      regularCauchyMinimum_round_trip,
      (fun _ _ heq => regularCauchyMinimumToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyMinimumUp.TasteGate
