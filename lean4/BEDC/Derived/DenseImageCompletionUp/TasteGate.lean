import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenseImageCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenseImageCompletionUp : Type where
  | mk (X E A M R S D H C P N : BHist) : DenseImageCompletionUp
  deriving DecidableEq

def denseImageCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denseImageCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denseImageCompletionEncodeBHist h

def denseImageCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denseImageCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denseImageCompletionDecodeBHist tail)

private theorem DenseImageCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def denseImageCompletionFields : DenseImageCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenseImageCompletionUp.mk X E A M R S D H C P N => [X, E, A, M, R, S, D, H, C, P, N]

def denseImageCompletionToEventFlow : DenseImageCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (denseImageCompletionFields x).map denseImageCompletionEncodeBHist

def denseImageCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => denseImageCompletionEventAtDefault index rest

def denseImageCompletionFromEventFlow (ef : EventFlow) : Option DenseImageCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenseImageCompletionUp.mk
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 0 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 1 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 2 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 3 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 4 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 5 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 6 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 7 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 8 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 9 ef))
      (denseImageCompletionDecodeBHist (denseImageCompletionEventAtDefault 10 ef)))

private theorem DenseImageCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DenseImageCompletionUp,
      denseImageCompletionFromEventFlow (denseImageCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X E A M R S D H C P N =>
      change
        some
          (DenseImageCompletionUp.mk
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist X))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist E))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist A))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist M))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist R))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist S))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist D))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist H))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist C))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist P))
            (denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist N))) =
          some (DenseImageCompletionUp.mk X E A M R S D H C P N)
      rw [DenseImageCompletionTasteGate_single_carrier_alignment_decode X,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode E,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode A,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode M,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode R,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode S,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode D,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode H,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode C,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode P,
        DenseImageCompletionTasteGate_single_carrier_alignment_decode N]

private theorem DenseImageCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DenseImageCompletionUp} :
    denseImageCompletionToEventFlow x = denseImageCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denseImageCompletionFromEventFlow (denseImageCompletionToEventFlow x) =
        denseImageCompletionFromEventFlow (denseImageCompletionToEventFlow y) :=
    congrArg denseImageCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DenseImageCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DenseImageCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem DenseImageCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : DenseImageCompletionUp, denseImageCompletionFields x = denseImageCompletionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 E1 A1 M1 R1 S1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 E2 A2 M2 R2 S2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance denseImageCompletionBHistCarrier : BHistCarrier DenseImageCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denseImageCompletionToEventFlow
  fromEventFlow := denseImageCompletionFromEventFlow

instance denseImageCompletionChapterTasteGate : ChapterTasteGate DenseImageCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denseImageCompletionFromEventFlow (denseImageCompletionToEventFlow x) = some x
    exact DenseImageCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DenseImageCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance denseImageCompletionFieldFaithful : FieldFaithful DenseImageCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := denseImageCompletionFields
  field_faithful := DenseImageCompletionTasteGate_single_carrier_alignment_fields

instance denseImageCompletionNontrivial : Nontrivial DenseImageCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DenseImageCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DenseImageCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DenseImageCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denseImageCompletionChapterTasteGate

theorem DenseImageCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DenseImageCompletionUp) ∧
      Nonempty (FieldFaithful DenseImageCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DenseImageCompletionUp) ∧
          (∀ h : BHist, denseImageCompletionDecodeBHist (denseImageCompletionEncodeBHist h) = h) ∧
            (∀ x : DenseImageCompletionUp,
              denseImageCompletionFromEventFlow (denseImageCompletionToEventFlow x) = some x) ∧
              (∀ x y : DenseImageCompletionUp,
                denseImageCompletionToEventFlow x = denseImageCompletionToEventFlow y → x = y) ∧
                denseImageCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨denseImageCompletionChapterTasteGate⟩,
      ⟨denseImageCompletionFieldFaithful⟩,
      ⟨denseImageCompletionNontrivial⟩,
      DenseImageCompletionTasteGate_single_carrier_alignment_decode,
      DenseImageCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DenseImageCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DenseImageCompletionUp
