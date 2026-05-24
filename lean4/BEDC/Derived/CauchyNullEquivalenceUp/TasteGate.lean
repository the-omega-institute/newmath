import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNullEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNullEquivalenceUp : Type where
  | mk (X Y D Z E H C P N : BHist) : CauchyNullEquivalenceUp
  deriving DecidableEq

def cauchyNullEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNullEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNullEquivalenceEncodeBHist h

def cauchyNullEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNullEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNullEquivalenceDecodeBHist tail)

private theorem CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNullEquivalenceFields : CauchyNullEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNullEquivalenceUp.mk X Y D Z E H C P N => [X, Y, D, Z, E, H, C, P, N]

def cauchyNullEquivalenceToEventFlow : CauchyNullEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNullEquivalenceFields x).map cauchyNullEquivalenceEncodeBHist

private def cauchyNullEquivalenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyNullEquivalenceEventAt index rest

def cauchyNullEquivalenceFromEventFlow (ef : EventFlow) :
    Option CauchyNullEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyNullEquivalenceUp.mk
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 0 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 1 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 2 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 3 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 4 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 5 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 6 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 7 ef))
      (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEventAt 8 ef)))

private theorem CauchyNullEquivalenceTasteGate_single_carrier_alignment_round_trip
    (x : CauchyNullEquivalenceUp) :
    cauchyNullEquivalenceFromEventFlow (cauchyNullEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y D Z E H C P N =>
      change
        some
          (CauchyNullEquivalenceUp.mk
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist X))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist Y))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist D))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist Z))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist E))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist H))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist C))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist P))
            (cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist N))) =
          some (CauchyNullEquivalenceUp.mk X Y D Z E H C P N)
      rw [CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode X,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode Y,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode E,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyNullEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyNullEquivalenceUp} :
    cauchyNullEquivalenceToEventFlow x = cauchyNullEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNullEquivalenceFromEventFlow (cauchyNullEquivalenceToEventFlow x) =
        cauchyNullEquivalenceFromEventFlow (cauchyNullEquivalenceToEventFlow y) :=
    congrArg cauchyNullEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyNullEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyNullEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyNullEquivalenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyNullEquivalenceUp,
      cauchyNullEquivalenceFields x = cauchyNullEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ D₁ Z₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ D₂ Z₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyNullEquivalenceBHistCarrier : BHistCarrier CauchyNullEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNullEquivalenceToEventFlow
  fromEventFlow := cauchyNullEquivalenceFromEventFlow

instance cauchyNullEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyNullEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyNullEquivalenceFromEventFlow (cauchyNullEquivalenceToEventFlow x) = some x
    exact CauchyNullEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyNullEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyNullEquivalenceFieldFaithful :
    FieldFaithful CauchyNullEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNullEquivalenceFields
  field_faithful := CauchyNullEquivalenceTasteGate_single_carrier_alignment_fields_faithful

instance cauchyNullEquivalenceNontrivial : Nontrivial CauchyNullEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNullEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyNullEquivalenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyNullEquivalenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyNullEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNullEquivalenceChapterTasteGate

theorem CauchyNullEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyNullEquivalenceDecodeBHist (cauchyNullEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchyNullEquivalenceUp,
        cauchyNullEquivalenceFromEventFlow (cauchyNullEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyNullEquivalenceUp,
          cauchyNullEquivalenceToEventFlow x = cauchyNullEquivalenceToEventFlow y → x = y) ∧
          cauchyNullEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyNullEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      CauchyNullEquivalenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyNullEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyNullEquivalenceUp
