import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowBaireCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowBaireCategoryUp : Type where
  | mk (M U D Q S R E T H C P N : BHist) : FiniteWindowBaireCategoryUp
  deriving DecidableEq

def finiteWindowBaireCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowBaireCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowBaireCategoryEncodeBHist h

def finiteWindowBaireCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowBaireCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowBaireCategoryDecodeBHist tail)

private theorem finiteWindowBaireCategory_decode_encode_bhist :
    ∀ h : BHist,
      finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteWindowBaireCategoryFields : FiniteWindowBaireCategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowBaireCategoryUp.mk M U D Q S R E T H C P N =>
      [M, U, D, Q, S, R, E, T, H, C, P, N]

def finiteWindowBaireCategoryToEventFlow : FiniteWindowBaireCategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteWindowBaireCategoryFields x).map finiteWindowBaireCategoryEncodeBHist

private def finiteWindowBaireCategoryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteWindowBaireCategoryEventAtDefault index rest

def finiteWindowBaireCategoryFromEventFlow
    (ef : EventFlow) : Option FiniteWindowBaireCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteWindowBaireCategoryUp.mk
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 0 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 1 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 2 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 3 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 4 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 5 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 6 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 7 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 8 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 9 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 10 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAtDefault 11 ef)))

private theorem finiteWindowBaireCategory_round_trip
    (x : FiniteWindowBaireCategoryUp) :
    finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M U D Q S R E T H C P N =>
      change
        some
          (FiniteWindowBaireCategoryUp.mk
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist M))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist U))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist D))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist Q))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist S))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist R))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist E))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist T))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist H))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist C))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist P))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist N))) =
          some (FiniteWindowBaireCategoryUp.mk M U D Q S R E T H C P N)
      rw [finiteWindowBaireCategory_decode_encode_bhist M]
      rw [finiteWindowBaireCategory_decode_encode_bhist U]
      rw [finiteWindowBaireCategory_decode_encode_bhist D]
      rw [finiteWindowBaireCategory_decode_encode_bhist Q]
      rw [finiteWindowBaireCategory_decode_encode_bhist S]
      rw [finiteWindowBaireCategory_decode_encode_bhist R]
      rw [finiteWindowBaireCategory_decode_encode_bhist E]
      rw [finiteWindowBaireCategory_decode_encode_bhist T]
      rw [finiteWindowBaireCategory_decode_encode_bhist H]
      rw [finiteWindowBaireCategory_decode_encode_bhist C]
      rw [finiteWindowBaireCategory_decode_encode_bhist P]
      rw [finiteWindowBaireCategory_decode_encode_bhist N]

private theorem finiteWindowBaireCategoryToEventFlow_injective
    {x y : FiniteWindowBaireCategoryUp} :
    finiteWindowBaireCategoryToEventFlow x = finiteWindowBaireCategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) =
        finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow y) :=
    congrArg finiteWindowBaireCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteWindowBaireCategory_round_trip x).symm
      (Eq.trans hread (finiteWindowBaireCategory_round_trip y)))

instance finiteWindowBaireCategoryBHistCarrier : BHistCarrier FiniteWindowBaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowBaireCategoryToEventFlow
  fromEventFlow := finiteWindowBaireCategoryFromEventFlow

instance finiteWindowBaireCategoryChapterTasteGate :
    ChapterTasteGate FiniteWindowBaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) =
      some x
    exact finiteWindowBaireCategory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowBaireCategoryToEventFlow_injective heq)

instance finiteWindowBaireCategoryFieldFaithful :
    FieldFaithful FiniteWindowBaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowBaireCategoryFields
  field_faithful := by
    intro x y h
    cases x with
    | mk M1 U1 D1 Q1 S1 R1 E1 T1 H1 C1 P1 N1 =>
        cases y with
        | mk M2 U2 D2 Q2 S2 R2 E2 T2 H2 C2 P2 N2 =>
            cases h
            rfl

instance finiteWindowBaireCategoryNontrivial : Nontrivial FiniteWindowBaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowBaireCategoryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FiniteWindowBaireCategoryUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteWindowBaireCategoryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteWindowBaireCategoryUp) ∧
      Nonempty (FieldFaithful FiniteWindowBaireCategoryUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteWindowBaireCategoryUp) ∧
          finiteWindowBaireCategoryEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ h : BHist,
              finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist h) =
                h) ∧
              (∀ x : FiniteWindowBaireCategoryUp,
                finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) =
                  some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨finiteWindowBaireCategoryChapterTasteGate⟩
  · constructor
    · exact ⟨finiteWindowBaireCategoryFieldFaithful⟩
    · constructor
      · exact ⟨finiteWindowBaireCategoryNontrivial⟩
      · constructor
        · rfl
        · constructor
          · intro h
            exact finiteWindowBaireCategory_decode_encode_bhist h
          · intro x
            exact finiteWindowBaireCategory_round_trip x

end BEDC.Derived.FiniteWindowBaireCategoryUp
