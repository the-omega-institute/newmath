import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealRootBracketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealRootBracketUp : Type where
  | mk (I S M V K W A R D E H C P N : BHist) : RealRootBracketUp
  deriving DecidableEq

def realRootBracketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realRootBracketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realRootBracketEncodeBHist h

def realRootBracketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realRootBracketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realRootBracketDecodeBHist tail)

private theorem RealRootBracketTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realRootBracketDecodeBHist (realRootBracketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realRootBracketToEventFlow : RealRootBracketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealRootBracketUp.mk I S M V K W A R D E H C P N =>
      [[BMark.b0],
        realRootBracketEncodeBHist I,
        [BMark.b1, BMark.b0],
        realRootBracketEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realRootBracketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realRootBracketEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realRootBracketEncodeBHist N]

private def realRootBracketEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realRootBracketEventAtDefault index rest

def realRootBracketFromEventFlow (ef : EventFlow) : Option RealRootBracketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealRootBracketUp.mk
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 1 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 3 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 5 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 7 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 9 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 11 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 13 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 15 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 17 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 19 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 21 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 23 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 25 ef))
      (realRootBracketDecodeBHist (realRootBracketEventAtDefault 27 ef)))

private theorem RealRootBracketTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealRootBracketUp,
      realRootBracketFromEventFlow (realRootBracketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S M V K W A R D E H C P N =>
      change
        some
          (RealRootBracketUp.mk
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist I))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist S))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist M))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist V))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist K))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist W))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist A))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist R))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist D))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist E))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist H))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist C))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist P))
            (realRootBracketDecodeBHist (realRootBracketEncodeBHist N))) =
          some (RealRootBracketUp.mk I S M V K W A R D E H C P N)
      rw [RealRootBracketTasteGate_single_carrier_alignment_decode I,
        RealRootBracketTasteGate_single_carrier_alignment_decode S,
        RealRootBracketTasteGate_single_carrier_alignment_decode M,
        RealRootBracketTasteGate_single_carrier_alignment_decode V,
        RealRootBracketTasteGate_single_carrier_alignment_decode K,
        RealRootBracketTasteGate_single_carrier_alignment_decode W,
        RealRootBracketTasteGate_single_carrier_alignment_decode A,
        RealRootBracketTasteGate_single_carrier_alignment_decode R,
        RealRootBracketTasteGate_single_carrier_alignment_decode D,
        RealRootBracketTasteGate_single_carrier_alignment_decode E,
        RealRootBracketTasteGate_single_carrier_alignment_decode H,
        RealRootBracketTasteGate_single_carrier_alignment_decode C,
        RealRootBracketTasteGate_single_carrier_alignment_decode P,
        RealRootBracketTasteGate_single_carrier_alignment_decode N]

private theorem RealRootBracketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealRootBracketUp} :
    realRootBracketToEventFlow x = realRootBracketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realRootBracketFromEventFlow (realRootBracketToEventFlow x) =
        realRootBracketFromEventFlow (realRootBracketToEventFlow y) :=
    congrArg realRootBracketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealRootBracketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealRootBracketTasteGate_single_carrier_alignment_round_trip y)))

private def realRootBracketFields : RealRootBracketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealRootBracketUp.mk I S M V K W A R D E H C P N => [I, S, M, V, K, W, A, R, D, E, H, C, P, N]

private theorem RealRootBracketTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealRootBracketUp, realRootBracketFields x = realRootBracketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 S1 M1 V1 K1 W1 A1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 S2 M2 V2 K2 W2 A2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realRootBracketBHistCarrier : BHistCarrier RealRootBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realRootBracketToEventFlow
  fromEventFlow := realRootBracketFromEventFlow

instance realRootBracketChapterTasteGate : ChapterTasteGate RealRootBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realRootBracketFromEventFlow (realRootBracketToEventFlow x) = some x
    exact RealRootBracketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealRootBracketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realRootBracketFieldFaithful : FieldFaithful RealRootBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realRootBracketFields
  field_faithful := RealRootBracketTasteGate_single_carrier_alignment_fields

instance realRootBracketNontrivial : Nontrivial RealRootBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealRootBracketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealRootBracketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealRootBracketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realRootBracketChapterTasteGate

theorem RealRootBracketTasteGate_single_carrier_alignment :
    (forall h : BHist, realRootBracketDecodeBHist (realRootBracketEncodeBHist h) = h) ∧
      (forall x : RealRootBracketUp,
        realRootBracketFromEventFlow (realRootBracketToEventFlow x) = some x) ∧
        (forall x y : RealRootBracketUp,
          realRootBracketToEventFlow x = realRootBracketToEventFlow y -> x = y) ∧
          realRootBracketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealRootBracketTasteGate_single_carrier_alignment_decode,
      RealRootBracketTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealRootBracketTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealRootBracketUp
