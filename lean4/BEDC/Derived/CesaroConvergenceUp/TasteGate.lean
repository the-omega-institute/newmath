import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CesaroConvergenceUp

namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CesaroConvergenceUp : Type where
  | mk (S M A L R E H T P N : BHist) : CesaroConvergenceUp
  deriving DecidableEq

def cesaroConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cesaroConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cesaroConvergenceEncodeBHist h

def cesaroConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cesaroConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cesaroConvergenceDecodeBHist tail)

private theorem CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cesaroConvergenceFields : CesaroConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CesaroConvergenceUp.mk S M A L R E H T P N => [S, M, A, L, R, E, H, T, P, N]

def cesaroConvergenceToEventFlow : CesaroConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cesaroConvergenceFields x).map cesaroConvergenceEncodeBHist

private def cesaroConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cesaroConvergenceEventAt index rest

def cesaroConvergenceFromEventFlow (ef : EventFlow) : Option CesaroConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CesaroConvergenceUp.mk
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 0 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 1 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 2 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 3 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 4 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 5 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 6 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 7 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 8 ef))
      (cesaroConvergenceDecodeBHist (cesaroConvergenceEventAt 9 ef)))

private theorem CesaroConvergenceTasteGate_single_carrier_alignment_round_trip
    (x : CesaroConvergenceUp) :
    cesaroConvergenceFromEventFlow (cesaroConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M A L R E H T P N =>
      change
        some
          (CesaroConvergenceUp.mk
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist S))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist M))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist A))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist L))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist R))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist E))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist H))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist T))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist P))
            (cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist N))) =
          some (CesaroConvergenceUp.mk S M A L R E H T P N)
      rw [CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode S,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode M,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode A,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode L,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode T,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CesaroConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CesaroConvergenceUp} :
    cesaroConvergenceToEventFlow x = cesaroConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cesaroConvergenceFromEventFlow (cesaroConvergenceToEventFlow x) =
        cesaroConvergenceFromEventFlow (cesaroConvergenceToEventFlow y) :=
    congrArg cesaroConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CesaroConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CesaroConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CesaroConvergenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CesaroConvergenceUp,
      cesaroConvergenceFields x = cesaroConvergenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ A₁ L₁ R₁ E₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ A₂ L₂ R₂ E₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance cesaroConvergenceBHistCarrier : BHistCarrier CesaroConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cesaroConvergenceToEventFlow
  fromEventFlow := cesaroConvergenceFromEventFlow

instance cesaroConvergenceChapterTasteGate : ChapterTasteGate CesaroConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cesaroConvergenceFromEventFlow (cesaroConvergenceToEventFlow x) = some x
    exact CesaroConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CesaroConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cesaroConvergenceFieldFaithful : FieldFaithful CesaroConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cesaroConvergenceFields
  field_faithful := CesaroConvergenceTasteGate_single_carrier_alignment_fields_faithful

instance cesaroConvergenceNontrivial : Nontrivial CesaroConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CesaroConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CesaroConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CesaroConvergenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CesaroConvergenceUp) ∧
      Nonempty (FieldFaithful CesaroConvergenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CesaroConvergenceUp) ∧
          (∀ h : BHist,
            cesaroConvergenceDecodeBHist (cesaroConvergenceEncodeBHist h) = h) ∧
            (∀ x : CesaroConvergenceUp,
              cesaroConvergenceFromEventFlow (cesaroConvergenceToEventFlow x) = some x) ∧
              (∀ x y : CesaroConvergenceUp,
                cesaroConvergenceToEventFlow x = cesaroConvergenceToEventFlow y → x = y) ∧
                cesaroConvergenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cesaroConvergenceChapterTasteGate⟩,
      ⟨cesaroConvergenceFieldFaithful⟩,
      ⟨cesaroConvergenceNontrivial⟩,
      CesaroConvergenceTasteGate_single_carrier_alignment_decode_encode,
      CesaroConvergenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CesaroConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.CesaroConvergenceUp
