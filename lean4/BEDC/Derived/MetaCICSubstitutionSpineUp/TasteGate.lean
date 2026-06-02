import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICSubstitutionSpineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICSubstitutionSpineUp : Type where
  | mk (T V D Q R L A H C P N : BHist) : MetaCICSubstitutionSpineUp
  deriving DecidableEq

def metacicSubstitutionSpineEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicSubstitutionSpineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicSubstitutionSpineEncodeBHist h

def metacicSubstitutionSpineDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicSubstitutionSpineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicSubstitutionSpineDecodeBHist tail)

private theorem metacicSubstitutionSpine_decode_encode :
    forall h : BHist,
      metacicSubstitutionSpineDecodeBHist
        (metacicSubstitutionSpineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metacicSubstitutionSpineFields : MetaCICSubstitutionSpineUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICSubstitutionSpineUp.mk T V D Q R L A H C P N =>
      [T, V, D, Q, R, L, A, H, C, P, N]

def metacicSubstitutionSpineToEventFlow : MetaCICSubstitutionSpineUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metacicSubstitutionSpineFields x).map metacicSubstitutionSpineEncodeBHist

private def metacicSubstitutionSpineEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metacicSubstitutionSpineEventAt index rest

def metacicSubstitutionSpineFromEventFlow
    (ef : EventFlow) : Option MetaCICSubstitutionSpineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICSubstitutionSpineUp.mk
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 0 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 1 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 2 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 3 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 4 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 5 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 6 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 7 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 8 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 9 ef))
      (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEventAt 10 ef)))

private theorem metacicSubstitutionSpine_round_trip
    (x : MetaCICSubstitutionSpineUp) :
    metacicSubstitutionSpineFromEventFlow (metacicSubstitutionSpineToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T V D Q R L A H C P N =>
      change
        some
          (MetaCICSubstitutionSpineUp.mk
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist T))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist V))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist D))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist Q))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist R))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist L))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist A))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist H))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist C))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist P))
            (metacicSubstitutionSpineDecodeBHist (metacicSubstitutionSpineEncodeBHist N))) =
          some (MetaCICSubstitutionSpineUp.mk T V D Q R L A H C P N)
      rw [metacicSubstitutionSpine_decode_encode T,
        metacicSubstitutionSpine_decode_encode V,
        metacicSubstitutionSpine_decode_encode D,
        metacicSubstitutionSpine_decode_encode Q,
        metacicSubstitutionSpine_decode_encode R,
        metacicSubstitutionSpine_decode_encode L,
        metacicSubstitutionSpine_decode_encode A,
        metacicSubstitutionSpine_decode_encode H,
        metacicSubstitutionSpine_decode_encode C,
        metacicSubstitutionSpine_decode_encode P,
        metacicSubstitutionSpine_decode_encode N]

private theorem metacicSubstitutionSpineToEventFlow_injective
    {x y : MetaCICSubstitutionSpineUp} :
    metacicSubstitutionSpineToEventFlow x = metacicSubstitutionSpineToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicSubstitutionSpineFromEventFlow (metacicSubstitutionSpineToEventFlow x) =
        metacicSubstitutionSpineFromEventFlow (metacicSubstitutionSpineToEventFlow y) :=
    congrArg metacicSubstitutionSpineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicSubstitutionSpine_round_trip x).symm
      (Eq.trans hread (metacicSubstitutionSpine_round_trip y)))

private theorem metacicSubstitutionSpineFields_faithful :
    forall x y : MetaCICSubstitutionSpineUp,
      metacicSubstitutionSpineFields x = metacicSubstitutionSpineFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 V1 D1 Q1 R1 L1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 V2 D2 Q2 R2 L2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metacicSubstitutionSpineBHistCarrier : BHistCarrier MetaCICSubstitutionSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicSubstitutionSpineToEventFlow
  fromEventFlow := metacicSubstitutionSpineFromEventFlow

instance metacicSubstitutionSpineChapterTasteGate :
    ChapterTasteGate MetaCICSubstitutionSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicSubstitutionSpineFromEventFlow (metacicSubstitutionSpineToEventFlow x) =
        some x
    exact metacicSubstitutionSpine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicSubstitutionSpineToEventFlow_injective heq)

instance metacicSubstitutionSpineFieldFaithful :
    FieldFaithful MetaCICSubstitutionSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicSubstitutionSpineFields
  field_faithful := metacicSubstitutionSpineFields_faithful

instance metacicSubstitutionSpineNontrivial :
    Nontrivial MetaCICSubstitutionSpineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICSubstitutionSpineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICSubstitutionSpineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICSubstitutionSpineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicSubstitutionSpineChapterTasteGate

theorem MetaCICSubstitutionSpineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICSubstitutionSpineUp) ∧
      Nonempty (FieldFaithful MetaCICSubstitutionSpineUp) ∧
        Nonempty (Nontrivial MetaCICSubstitutionSpineUp) ∧
          (forall h : BHist,
            metacicSubstitutionSpineDecodeBHist
              (metacicSubstitutionSpineEncodeBHist h) = h) ∧
            (forall x : MetaCICSubstitutionSpineUp,
              metacicSubstitutionSpineFromEventFlow
                  (metacicSubstitutionSpineToEventFlow x) = some x) ∧
              (forall x y : MetaCICSubstitutionSpineUp,
                metacicSubstitutionSpineToEventFlow x =
                    metacicSubstitutionSpineToEventFlow y ->
                  x = y) ∧
                metacicSubstitutionSpineEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨metacicSubstitutionSpineChapterTasteGate⟩,
      ⟨metacicSubstitutionSpineFieldFaithful⟩,
      ⟨metacicSubstitutionSpineNontrivial⟩,
      metacicSubstitutionSpine_decode_encode,
      metacicSubstitutionSpine_round_trip,
      (fun _ _ heq => metacicSubstitutionSpineToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICSubstitutionSpineUp
