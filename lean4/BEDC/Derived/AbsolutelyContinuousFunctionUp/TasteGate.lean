import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbsolutelyContinuousFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbsolutelyContinuousFunctionUp : Type where
  | mk (I F M P V D L T W Q R H C S N : BHist) : AbsolutelyContinuousFunctionUp
  deriving DecidableEq

def absolutelyContinuousFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: absolutelyContinuousFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: absolutelyContinuousFunctionEncodeBHist h

def absolutelyContinuousFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (absolutelyContinuousFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (absolutelyContinuousFunctionDecodeBHist tail)

private theorem AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      absolutelyContinuousFunctionDecodeBHist
        (absolutelyContinuousFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def absolutelyContinuousFunctionFields : AbsolutelyContinuousFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbsolutelyContinuousFunctionUp.mk I F M P V D L T W Q R H C S N =>
      [I, F, M, P, V, D, L, T, W, Q, R, H, C, S, N]

def absolutelyContinuousFunctionToEventFlow : AbsolutelyContinuousFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (absolutelyContinuousFunctionFields x).map absolutelyContinuousFunctionEncodeBHist

def absolutelyContinuousFunctionFromEventFlow :
    EventFlow → Option AbsolutelyContinuousFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: F :: M :: P :: V :: D :: L :: T :: W :: Q :: R :: H :: C :: S :: N :: [] =>
      some
        (AbsolutelyContinuousFunctionUp.mk
          (absolutelyContinuousFunctionDecodeBHist I)
          (absolutelyContinuousFunctionDecodeBHist F)
          (absolutelyContinuousFunctionDecodeBHist M)
          (absolutelyContinuousFunctionDecodeBHist P)
          (absolutelyContinuousFunctionDecodeBHist V)
          (absolutelyContinuousFunctionDecodeBHist D)
          (absolutelyContinuousFunctionDecodeBHist L)
          (absolutelyContinuousFunctionDecodeBHist T)
          (absolutelyContinuousFunctionDecodeBHist W)
          (absolutelyContinuousFunctionDecodeBHist Q)
          (absolutelyContinuousFunctionDecodeBHist R)
          (absolutelyContinuousFunctionDecodeBHist H)
          (absolutelyContinuousFunctionDecodeBHist C)
          (absolutelyContinuousFunctionDecodeBHist S)
          (absolutelyContinuousFunctionDecodeBHist N))
  | _ => none

private theorem AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_round_trip
    (x : AbsolutelyContinuousFunctionUp) :
    absolutelyContinuousFunctionFromEventFlow
      (absolutelyContinuousFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F M P V D L T W Q R H C S N =>
      change
        some
          (AbsolutelyContinuousFunctionUp.mk
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist I))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist F))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist M))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist P))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist V))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist D))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist L))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist T))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist W))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist Q))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist R))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist H))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist C))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist S))
            (absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist N))) =
          some (AbsolutelyContinuousFunctionUp.mk I F M P V D L T W Q R H C S N)
      rw [AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode I,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode F,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode M,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode P,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode V,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode D,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode L,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode T,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode W,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode Q,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode R,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode H,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode C,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode S,
        AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbsolutelyContinuousFunctionUp} :
    absolutelyContinuousFunctionToEventFlow x =
      absolutelyContinuousFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      absolutelyContinuousFunctionFromEventFlow (absolutelyContinuousFunctionToEventFlow x) =
        absolutelyContinuousFunctionFromEventFlow (absolutelyContinuousFunctionToEventFlow y) :=
    congrArg absolutelyContinuousFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AbsolutelyContinuousFunctionUp,
      absolutelyContinuousFunctionFields x = absolutelyContinuousFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ M₁ P₁ V₁ D₁ L₁ T₁ W₁ Q₁ R₁ H₁ C₁ S₁ N₁ =>
      cases y with
      | mk I₂ F₂ M₂ P₂ V₂ D₂ L₂ T₂ W₂ Q₂ R₂ H₂ C₂ S₂ N₂ =>
          cases hfields
          rfl

instance absolutelyContinuousFunctionBHistCarrier :
    BHistCarrier AbsolutelyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := absolutelyContinuousFunctionToEventFlow
  fromEventFlow := absolutelyContinuousFunctionFromEventFlow

instance absolutelyContinuousFunctionChapterTasteGate :
    ChapterTasteGate AbsolutelyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      absolutelyContinuousFunctionFromEventFlow
        (absolutelyContinuousFunctionToEventFlow x) = some x
    exact AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance absolutelyContinuousFunctionFieldFaithful :
    FieldFaithful AbsolutelyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := absolutelyContinuousFunctionFields
  field_faithful :=
    AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_fields_faithful

instance absolutelyContinuousFunctionNontrivial : Nontrivial AbsolutelyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbsolutelyContinuousFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AbsolutelyContinuousFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate AbsolutelyContinuousFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  absolutelyContinuousFunctionChapterTasteGate

theorem AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AbsolutelyContinuousFunctionUp) ∧
      Nonempty (FieldFaithful AbsolutelyContinuousFunctionUp) ∧
        Nonempty (Nontrivial AbsolutelyContinuousFunctionUp) ∧
          (∀ h : BHist,
            absolutelyContinuousFunctionDecodeBHist
              (absolutelyContinuousFunctionEncodeBHist h) = h) ∧
            (∀ x : AbsolutelyContinuousFunctionUp,
              absolutelyContinuousFunctionFromEventFlow
                (absolutelyContinuousFunctionToEventFlow x) = some x) ∧
              (∀ x y : AbsolutelyContinuousFunctionUp,
                absolutelyContinuousFunctionToEventFlow x =
                  absolutelyContinuousFunctionToEventFlow y → x = y) ∧
                absolutelyContinuousFunctionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨absolutelyContinuousFunctionChapterTasteGate⟩
  · constructor
    · exact ⟨absolutelyContinuousFunctionFieldFaithful⟩
    · constructor
      · exact ⟨absolutelyContinuousFunctionNontrivial⟩
      · constructor
        · exact AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                AbsolutelyContinuousFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.AbsolutelyContinuousFunctionUp
