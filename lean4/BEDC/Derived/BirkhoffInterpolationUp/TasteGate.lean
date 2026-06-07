import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BirkhoffInterpolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BirkhoffInterpolationUp : Type where
  | mk (X M V P A L S H C R N : BHist) : BirkhoffInterpolationUp
  deriving DecidableEq

def birkhoffInterpolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: birkhoffInterpolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: birkhoffInterpolationEncodeBHist h

def birkhoffInterpolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (birkhoffInterpolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (birkhoffInterpolationDecodeBHist tail)

private theorem BirkhoffInterpolationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def birkhoffInterpolationFields : BirkhoffInterpolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BirkhoffInterpolationUp.mk X M V P A L S H C R N => [X, M, V, P, A, L, S, H, C, R, N]

def birkhoffInterpolationToEventFlow : BirkhoffInterpolationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (birkhoffInterpolationFields x).map birkhoffInterpolationEncodeBHist

private def birkhoffInterpolationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => birkhoffInterpolationEventAtDefault index rest

def birkhoffInterpolationFromEventFlow
    (ef : EventFlow) : Option BirkhoffInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BirkhoffInterpolationUp.mk
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 0 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 1 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 2 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 3 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 4 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 5 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 6 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 7 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 8 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 9 ef))
      (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEventAtDefault 10 ef)))

private theorem BirkhoffInterpolationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BirkhoffInterpolationUp,
      birkhoffInterpolationFromEventFlow (birkhoffInterpolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M V P A L S H C R N =>
      change
        some
          (BirkhoffInterpolationUp.mk
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist X))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist M))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist V))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist P))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist A))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist L))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist S))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist H))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist C))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist R))
            (birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist N))) =
          some (BirkhoffInterpolationUp.mk X M V P A L S H C R N)
      rw [BirkhoffInterpolationTasteGate_single_carrier_alignment_decode X,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode M,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode V,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode P,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode A,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode L,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode S,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode H,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode C,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode R,
        BirkhoffInterpolationTasteGate_single_carrier_alignment_decode N]

private theorem BirkhoffInterpolationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BirkhoffInterpolationUp} :
    birkhoffInterpolationToEventFlow x = birkhoffInterpolationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      birkhoffInterpolationFromEventFlow (birkhoffInterpolationToEventFlow x) =
        birkhoffInterpolationFromEventFlow (birkhoffInterpolationToEventFlow y) :=
    congrArg birkhoffInterpolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BirkhoffInterpolationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BirkhoffInterpolationTasteGate_single_carrier_alignment_round_trip y)))

private theorem BirkhoffInterpolationTasteGate_single_carrier_alignment_fields :
    ∀ x y : BirkhoffInterpolationUp,
      birkhoffInterpolationFields x = birkhoffInterpolationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ M₁ V₁ P₁ A₁ L₁ S₁ H₁ C₁ R₁ N₁ =>
      cases y with
      | mk X₂ M₂ V₂ P₂ A₂ L₂ S₂ H₂ C₂ R₂ N₂ =>
          cases hfields
          rfl

instance birkhoffInterpolationBHistCarrier :
    BHistCarrier BirkhoffInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := birkhoffInterpolationToEventFlow
  fromEventFlow := birkhoffInterpolationFromEventFlow

instance birkhoffInterpolationChapterTasteGate :
    ChapterTasteGate BirkhoffInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      birkhoffInterpolationFromEventFlow (birkhoffInterpolationToEventFlow x) = some x
    exact BirkhoffInterpolationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BirkhoffInterpolationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance birkhoffInterpolationFieldFaithful :
    FieldFaithful BirkhoffInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := birkhoffInterpolationFields
  field_faithful := BirkhoffInterpolationTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate BirkhoffInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  birkhoffInterpolationChapterTasteGate

theorem BirkhoffInterpolationTasteGate_single_carrier_alignment :
    (∀ h : BHist, birkhoffInterpolationDecodeBHist (birkhoffInterpolationEncodeBHist h) = h) ∧
      (∀ x : BirkhoffInterpolationUp,
        birkhoffInterpolationFromEventFlow (birkhoffInterpolationToEventFlow x) = some x) ∧
        (∀ x y : BirkhoffInterpolationUp,
          birkhoffInterpolationToEventFlow x = birkhoffInterpolationToEventFlow y → x = y) ∧
          birkhoffInterpolationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨BirkhoffInterpolationTasteGate_single_carrier_alignment_decode,
      BirkhoffInterpolationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BirkhoffInterpolationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BirkhoffInterpolationUp
