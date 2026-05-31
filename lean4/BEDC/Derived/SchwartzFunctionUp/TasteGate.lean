import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwartzFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwartzFunctionUp : Type where
  | mk (D W G F T R L H C P N : BHist) : SchwartzFunctionUp
  deriving DecidableEq

def schwartzFunctionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwartzFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwartzFunctionEncodeBHist h

def schwartzFunctionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwartzFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwartzFunctionDecodeBHist tail)

private theorem SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwartzFunctionFields : SchwartzFunctionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwartzFunctionUp.mk D W G F T R L H C P N => [D, W, G, F, T, R, L, H, C, P, N]

def schwartzFunctionToEventFlow : SchwartzFunctionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (schwartzFunctionFields x).map schwartzFunctionEncodeBHist

private def schwartzFunctionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schwartzFunctionEventAtDefault index rest

def schwartzFunctionFromEventFlow : EventFlow -> Option SchwartzFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SchwartzFunctionUp.mk
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 0 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 1 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 2 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 3 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 4 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 5 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 6 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 7 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 8 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 9 ef))
          (schwartzFunctionDecodeBHist (schwartzFunctionEventAtDefault 10 ef)))

private theorem SchwartzFunctionTasteGate_single_carrier_alignment_round_trip :
    forall x : SchwartzFunctionUp,
      schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W G F T R L H C P N =>
      change
        some
          (SchwartzFunctionUp.mk
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist D))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist W))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist G))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist F))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist T))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist R))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist L))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist H))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist C))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist P))
            (schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist N))) =
          some (SchwartzFunctionUp.mk D W G F T R L H C P N)
      rw [SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode D,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode W,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode G,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode F,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode T,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode R,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode L,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode H,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode C,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode P,
        SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem SchwartzFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchwartzFunctionUp} :
    schwartzFunctionToEventFlow x = schwartzFunctionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) =
        schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow y) :=
    congrArg schwartzFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SchwartzFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SchwartzFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem SchwartzFunctionTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : SchwartzFunctionUp, schwartzFunctionFields x = schwartzFunctionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 W1 G1 F1 T1 R1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 W2 G2 F2 T2 R2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance schwartzFunctionBHistCarrier : BHistCarrier SchwartzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwartzFunctionToEventFlow
  fromEventFlow := schwartzFunctionFromEventFlow

instance schwartzFunctionChapterTasteGate : ChapterTasteGate SchwartzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) = some x
    exact SchwartzFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchwartzFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance schwartzFunctionFieldFaithful : FieldFaithful SchwartzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := schwartzFunctionFields
  field_faithful := SchwartzFunctionTasteGate_single_carrier_alignment_fields_faithful

instance schwartzFunctionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SchwartzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SchwartzFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SchwartzFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SchwartzFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schwartzFunctionChapterTasteGate

theorem SchwartzFunctionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SchwartzFunctionUp) ∧
      Nonempty (FieldFaithful SchwartzFunctionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SchwartzFunctionUp) ∧
          (∀ h : BHist, schwartzFunctionDecodeBHist (schwartzFunctionEncodeBHist h) = h) ∧
            (∀ x : SchwartzFunctionUp,
              schwartzFunctionFromEventFlow (schwartzFunctionToEventFlow x) = some x) ∧
              (∀ x y : SchwartzFunctionUp,
                schwartzFunctionToEventFlow x = schwartzFunctionToEventFlow y -> x = y) ∧
                schwartzFunctionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨schwartzFunctionChapterTasteGate⟩,
      ⟨⟨schwartzFunctionFieldFaithful⟩,
        ⟨⟨schwartzFunctionNontrivial⟩,
          ⟨SchwartzFunctionTasteGate_single_carrier_alignment_decode_encode,
            ⟨SchwartzFunctionTasteGate_single_carrier_alignment_round_trip,
              ⟨(fun _ _ heq =>
                SchwartzFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.SchwartzFunctionUp.TasteGate
