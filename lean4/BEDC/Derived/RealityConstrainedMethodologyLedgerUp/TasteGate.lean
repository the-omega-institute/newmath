import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedMethodologyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedMethodologyLedgerUp : Type where
  | mk (X A O T I S D U F H C Q N : BHist) : RealityConstrainedMethodologyLedgerUp
  deriving DecidableEq

def realityConstrainedMethodologyLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedMethodologyLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedMethodologyLedgerEncodeBHist h

def realityConstrainedMethodologyLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedMethodologyLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedMethodologyLedgerDecodeBHist tail)

private theorem RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedMethodologyLedgerFields :
    RealityConstrainedMethodologyLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedMethodologyLedgerUp.mk X A O T I S D U F H C Q N =>
      [X, A, O, T, I, S, D, U, F, H, C, Q, N]

def realityConstrainedMethodologyLedgerToEventFlow :
    RealityConstrainedMethodologyLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedMethodologyLedgerUp.mk X A O T I S D U F H C Q N =>
      [[BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist X,
        [BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedMethodologyLedgerEncodeBHist N]

private def realityConstrainedMethodologyLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realityConstrainedMethodologyLedgerEventAtDefault index rest

def realityConstrainedMethodologyLedgerFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedMethodologyLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedMethodologyLedgerUp.mk
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 1 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 3 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 5 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 7 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 9 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 11 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 13 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 15 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 17 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 19 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 21 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 23 ef))
      (realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEventAtDefault 25 ef)))

private theorem RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_round_trip :
    forall x : RealityConstrainedMethodologyLedgerUp,
      realityConstrainedMethodologyLedgerFromEventFlow
        (realityConstrainedMethodologyLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A O T I S D U F H C Q N =>
      change
        some
          (RealityConstrainedMethodologyLedgerUp.mk
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist X))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist A))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist O))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist T))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist I))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist S))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist D))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist U))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist F))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist H))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist C))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist Q))
            (realityConstrainedMethodologyLedgerDecodeBHist
              (realityConstrainedMethodologyLedgerEncodeBHist N))) =
          some (RealityConstrainedMethodologyLedgerUp.mk X A O T I S D U F H C Q N)
      rw [RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode X,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode A,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode O,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode T,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode I,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode S,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode D,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode U,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode F,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode H,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode C,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode Q,
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode N]

private theorem RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_injective
    {x y : RealityConstrainedMethodologyLedgerUp} :
    realityConstrainedMethodologyLedgerToEventFlow x =
      realityConstrainedMethodologyLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedMethodologyLedgerFromEventFlow
          (realityConstrainedMethodologyLedgerToEventFlow x) =
        realityConstrainedMethodologyLedgerFromEventFlow
          (realityConstrainedMethodologyLedgerToEventFlow y) :=
    congrArg realityConstrainedMethodologyLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_fields :
    forall x y : RealityConstrainedMethodologyLedgerUp,
      realityConstrainedMethodologyLedgerFields x =
        realityConstrainedMethodologyLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 O1 T1 I1 S1 D1 U1 F1 H1 C1 Q1 N1 =>
      cases y with
      | mk X2 A2 O2 T2 I2 S2 D2 U2 F2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance realityConstrainedMethodologyLedgerBHistCarrier :
    BHistCarrier RealityConstrainedMethodologyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedMethodologyLedgerToEventFlow
  fromEventFlow := realityConstrainedMethodologyLedgerFromEventFlow

instance realityConstrainedMethodologyLedgerChapterTasteGate :
    ChapterTasteGate RealityConstrainedMethodologyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedMethodologyLedgerFromEventFlow
        (realityConstrainedMethodologyLedgerToEventFlow x) = some x
    exact RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_injective heq)

instance realityConstrainedMethodologyLedgerFieldFaithful :
    FieldFaithful RealityConstrainedMethodologyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedMethodologyLedgerFields
  field_faithful := RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_fields

instance realityConstrainedMethodologyLedgerNontrivial :
    Nontrivial RealityConstrainedMethodologyLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedMethodologyLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedMethodologyLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realityConstrainedMethodologyLedgerDecodeBHist
        (realityConstrainedMethodologyLedgerEncodeBHist h) = h) ∧
      (forall x : RealityConstrainedMethodologyLedgerUp,
        realityConstrainedMethodologyLedgerFromEventFlow
          (realityConstrainedMethodologyLedgerToEventFlow x) = some x) ∧
        (forall x y : RealityConstrainedMethodologyLedgerUp,
          realityConstrainedMethodologyLedgerToEventFlow x =
            realityConstrainedMethodologyLedgerToEventFlow y -> x = y) ∧
          realityConstrainedMethodologyLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_decode,
      RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealityConstrainedMethodologyLedgerTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.RealityConstrainedMethodologyLedgerUp
