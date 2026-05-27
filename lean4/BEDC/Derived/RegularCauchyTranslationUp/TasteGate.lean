import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTranslationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTranslationUp : Type where
  | mk (X Q WX WQ DX DQ A E R Z H C P N : BHist) : RegularCauchyTranslationUp
  deriving DecidableEq

def regularCauchyTranslationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTranslationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTranslationEncodeBHist h

def regularCauchyTranslationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTranslationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTranslationDecodeBHist tail)

private theorem regularCauchyTranslation_decode_encode :
    ∀ h : BHist,
      regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTranslationFields : RegularCauchyTranslationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTranslationUp.mk X Q WX WQ DX DQ A E R Z H C P N =>
      [X, Q, WX, WQ, DX, DQ, A, E, R, Z, H, C, P, N]

def regularCauchyTranslationToEventFlow : RegularCauchyTranslationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyTranslationFields x).map regularCauchyTranslationEncodeBHist

private def regularCauchyTranslationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTranslationEventAtDefault index rest

def regularCauchyTranslationFromEventFlow (ef : EventFlow) :
    Option RegularCauchyTranslationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTranslationUp.mk
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 0 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 1 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 2 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 3 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 4 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 5 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 6 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 7 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 8 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 9 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 10 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 11 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 12 ef))
      (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEventAtDefault 13 ef)))

private theorem regularCauchyTranslation_round_trip :
    ∀ x : RegularCauchyTranslationUp,
      regularCauchyTranslationFromEventFlow
        (regularCauchyTranslationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Q WX WQ DX DQ A E R Z H C P N =>
      change
        some
          (RegularCauchyTranslationUp.mk
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist X))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist Q))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist WX))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist WQ))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist DX))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist DQ))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist A))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist E))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist R))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist Z))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist H))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist C))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist P))
            (regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist N))) =
          some (RegularCauchyTranslationUp.mk X Q WX WQ DX DQ A E R Z H C P N)
      rw [regularCauchyTranslation_decode_encode X, regularCauchyTranslation_decode_encode Q,
        regularCauchyTranslation_decode_encode WX, regularCauchyTranslation_decode_encode WQ,
        regularCauchyTranslation_decode_encode DX, regularCauchyTranslation_decode_encode DQ,
        regularCauchyTranslation_decode_encode A, regularCauchyTranslation_decode_encode E,
        regularCauchyTranslation_decode_encode R, regularCauchyTranslation_decode_encode Z,
        regularCauchyTranslation_decode_encode H, regularCauchyTranslation_decode_encode C,
        regularCauchyTranslation_decode_encode P, regularCauchyTranslation_decode_encode N]

private theorem regularCauchyTranslationToEventFlow_injective
    {x y : RegularCauchyTranslationUp} :
    regularCauchyTranslationToEventFlow x =
      regularCauchyTranslationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTranslationFromEventFlow (regularCauchyTranslationToEventFlow x) =
        regularCauchyTranslationFromEventFlow (regularCauchyTranslationToEventFlow y) :=
    congrArg regularCauchyTranslationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTranslation_round_trip x).symm
      (Eq.trans hread (regularCauchyTranslation_round_trip y)))

private theorem regularCauchyTranslation_field_faithful :
    ∀ x y : RegularCauchyTranslationUp,
      regularCauchyTranslationFields x = regularCauchyTranslationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Q₁ WX₁ WQ₁ DX₁ DQ₁ A₁ E₁ R₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Q₂ WX₂ WQ₂ DX₂ DQ₂ A₂ E₂ R₂ Z₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyTranslationBHistCarrier : BHistCarrier RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTranslationToEventFlow
  fromEventFlow := regularCauchyTranslationFromEventFlow

instance regularCauchyTranslationChapterTasteGate :
    ChapterTasteGate RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTranslationFromEventFlow
      (regularCauchyTranslationToEventFlow x) = some x
    exact regularCauchyTranslation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTranslationToEventFlow_injective heq)

instance regularCauchyTranslationFieldFaithful :
    FieldFaithful RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTranslationFields
  field_faithful := regularCauchyTranslation_field_faithful

instance regularCauchyTranslationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTranslationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTranslationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTranslationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTranslationChapterTasteGate

theorem RegularCauchyTranslationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyTranslationUp) ∧
      Nonempty (FieldFaithful RegularCauchyTranslationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyTranslationUp) ∧
          (∀ h : BHist,
            regularCauchyTranslationDecodeBHist
              (regularCauchyTranslationEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyTranslationUp,
              regularCauchyTranslationFromEventFlow
                (regularCauchyTranslationToEventFlow x) = some x) ∧
              (∀ x y : RegularCauchyTranslationUp,
                regularCauchyTranslationToEventFlow x =
                  regularCauchyTranslationToEventFlow y -> x = y) ∧
                regularCauchyTranslationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨regularCauchyTranslationChapterTasteGate⟩,
      ⟨regularCauchyTranslationFieldFaithful⟩,
      ⟨regularCauchyTranslationNontrivial⟩,
      regularCauchyTranslation_decode_encode,
      regularCauchyTranslation_round_trip,
      (fun _ _ heq => regularCauchyTranslationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyTranslationUp
