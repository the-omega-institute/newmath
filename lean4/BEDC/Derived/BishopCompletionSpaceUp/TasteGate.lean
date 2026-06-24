import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionSpaceUp : Type where
  | mk (X Q D R E F H C P N : BHist) : BishopCompletionSpaceUp
  deriving DecidableEq

def bishopCompletionSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionSpaceEncodeBHist h

def bishopCompletionSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionSpaceDecodeBHist tail)

private theorem BishopCompletionSpaceTasteGate_single_carrier_alignment_decode :
    forall h : BHist, bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def bishopCompletionSpaceFields : BishopCompletionSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionSpaceUp.mk X Q D R E F H C P N => [X, Q, D, R, E, F, H, C, P, N]

def bishopCompletionSpaceToEventFlow : BishopCompletionSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCompletionSpaceFields x).map bishopCompletionSpaceEncodeBHist

private def bishopCompletionSpaceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionSpaceEventAtDefault index rest

def bishopCompletionSpaceFromEventFlow (ef : EventFlow) : Option BishopCompletionSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCompletionSpaceUp.mk
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 0 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 1 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 2 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 3 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 4 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 5 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 6 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 7 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 8 ef))
      (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEventAtDefault 9 ef)))

private theorem BishopCompletionSpaceTasteGate_single_carrier_alignment_round_trip :
    forall x : BishopCompletionSpaceUp,
      bishopCompletionSpaceFromEventFlow (bishopCompletionSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Q D R E F H C P N =>
      change
        some
          (BishopCompletionSpaceUp.mk
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist X))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist Q))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist D))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist R))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist E))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist F))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist H))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist C))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist P))
            (bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist N))) =
          some (BishopCompletionSpaceUp.mk X Q D R E F H C P N)
      rw [BishopCompletionSpaceTasteGate_single_carrier_alignment_decode X,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode Q,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode D,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode R,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode E,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode F,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode H,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode C,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode P,
        BishopCompletionSpaceTasteGate_single_carrier_alignment_decode N]

private theorem BishopCompletionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompletionSpaceUp} :
    bishopCompletionSpaceToEventFlow x = bishopCompletionSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionSpaceFromEventFlow (bishopCompletionSpaceToEventFlow x) =
        bishopCompletionSpaceFromEventFlow (bishopCompletionSpaceToEventFlow y) :=
    congrArg bishopCompletionSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompletionSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopCompletionSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCompletionSpaceTasteGate_single_carrier_alignment_fields :
    forall x y : BishopCompletionSpaceUp,
      bishopCompletionSpaceFields x = bishopCompletionSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Q1 D1 R1 E1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Q2 D2 R2 E2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCompletionSpaceBHistCarrier : BHistCarrier BishopCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionSpaceToEventFlow
  fromEventFlow := bishopCompletionSpaceFromEventFlow

instance bishopCompletionSpaceChapterTasteGate : ChapterTasteGate BishopCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompletionSpaceFromEventFlow (bishopCompletionSpaceToEventFlow x) = some x
    exact BishopCompletionSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCompletionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopCompletionSpaceFieldFaithful : FieldFaithful BishopCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompletionSpaceFields
  field_faithful := BishopCompletionSpaceTasteGate_single_carrier_alignment_fields

instance bishopCompletionSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopCompletionSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompletionSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCompletionSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopCompletionSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopCompletionSpaceUp) ∧
      Nonempty (FieldFaithful BishopCompletionSpaceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopCompletionSpaceUp) ∧
      (∀ h : BHist, bishopCompletionSpaceDecodeBHist (bishopCompletionSpaceEncodeBHist h) = h) ∧
      (∀ x : BishopCompletionSpaceUp,
        bishopCompletionSpaceFromEventFlow (bishopCompletionSpaceToEventFlow x) = some x) ∧
      (∀ x y : BishopCompletionSpaceUp,
        bishopCompletionSpaceToEventFlow x = bishopCompletionSpaceToEventFlow y -> x = y) ∧
      bishopCompletionSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨bishopCompletionSpaceChapterTasteGate⟩,
      ⟨bishopCompletionSpaceFieldFaithful⟩,
      ⟨bishopCompletionSpaceNontrivial⟩,
      BishopCompletionSpaceTasteGate_single_carrier_alignment_decode,
      BishopCompletionSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BishopCompletionSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopCompletionSpaceUp.TasteGate
