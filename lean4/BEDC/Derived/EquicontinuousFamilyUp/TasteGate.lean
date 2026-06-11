import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuousFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuousFamilyUp : Type where
  | mk (X F J M S R V H C P N : BHist) : EquicontinuousFamilyUp
  deriving DecidableEq

def equicontinuousFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuousFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuousFamilyEncodeBHist h

def equicontinuousFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuousFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuousFamilyDecodeBHist tail)

private theorem equicontinuousFamilyDecode_encode_bhist :
    ∀ h : BHist, equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuousFamilyFields : EquicontinuousFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuousFamilyUp.mk X F J M S R V H C P N => [X, F, J, M, S, R, V, H, C, P, N]

def equicontinuousFamilyToEventFlow : EquicontinuousFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (equicontinuousFamilyFields x).map equicontinuousFamilyEncodeBHist

private def equicontinuousFamilyRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => equicontinuousFamilyRawAt index rest

private def equicontinuousFamilyLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => equicontinuousFamilyLengthEq index rest

def equicontinuousFamilyFromEventFlow : EventFlow → Option EquicontinuousFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match equicontinuousFamilyLengthEq 11 flow with
      | true =>
          some
            (EquicontinuousFamilyUp.mk
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 0 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 1 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 2 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 3 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 4 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 5 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 6 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 7 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 8 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 9 flow))
              (equicontinuousFamilyDecodeBHist (equicontinuousFamilyRawAt 10 flow)))
      | false => none

private theorem equicontinuousFamily_round_trip :
    ∀ x : EquicontinuousFamilyUp,
      equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F J M S R V H C P N =>
      change
        some
          (EquicontinuousFamilyUp.mk
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist X))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist F))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist J))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist M))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist S))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist R))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist V))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist H))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist C))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist P))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist N))) =
          some (EquicontinuousFamilyUp.mk X F J M S R V H C P N)
      rw [equicontinuousFamilyDecode_encode_bhist X,
        equicontinuousFamilyDecode_encode_bhist F,
        equicontinuousFamilyDecode_encode_bhist J,
        equicontinuousFamilyDecode_encode_bhist M,
        equicontinuousFamilyDecode_encode_bhist S,
        equicontinuousFamilyDecode_encode_bhist R,
        equicontinuousFamilyDecode_encode_bhist V,
        equicontinuousFamilyDecode_encode_bhist H,
        equicontinuousFamilyDecode_encode_bhist C,
        equicontinuousFamilyDecode_encode_bhist P,
        equicontinuousFamilyDecode_encode_bhist N]

private theorem equicontinuousFamilyToEventFlow_injective {x y : EquicontinuousFamilyUp} :
    equicontinuousFamilyToEventFlow x = equicontinuousFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) =
        equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow y) :=
    congrArg equicontinuousFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (equicontinuousFamily_round_trip x).symm
      (Eq.trans hread (equicontinuousFamily_round_trip y)))

instance equicontinuousFamilyBHistCarrier : BHistCarrier EquicontinuousFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuousFamilyToEventFlow
  fromEventFlow := equicontinuousFamilyFromEventFlow

instance equicontinuousFamilyChapterTasteGate :
    ChapterTasteGate EquicontinuousFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) = some x
    exact equicontinuousFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (equicontinuousFamilyToEventFlow_injective heq)

instance equicontinuousFamilyFieldFaithful : FieldFaithful EquicontinuousFamilyUp where
  fields := equicontinuousFamilyFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk X₁ F₁ J₁ M₁ S₁ R₁ V₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk X₂ F₂ J₂ M₂ S₂ R₂ V₂ H₂ C₂ P₂ N₂ =>
            injection h with hX hTail₁
            injection hTail₁ with hF hTail₂
            injection hTail₂ with hJ hTail₃
            injection hTail₃ with hM hTail₄
            injection hTail₄ with hS hTail₅
            injection hTail₅ with hR hTail₆
            injection hTail₆ with hV hTail₇
            injection hTail₇ with hH hTail₈
            injection hTail₈ with hC hTail₉
            injection hTail₉ with hP hTail₁₀
            injection hTail₁₀ with hN _
            subst hX
            subst hF
            subst hJ
            subst hM
            subst hS
            subst hR
            subst hV
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance equicontinuousFamilyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EquicontinuousFamilyUp where
  witness_pair :=
    ⟨EquicontinuousFamilyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EquicontinuousFamilyUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        injection h with hX _rest
        cases hX⟩

def taste_gate : ChapterTasteGate EquicontinuousFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  equicontinuousFamilyChapterTasteGate

theorem EquicontinuousFamilyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EquicontinuousFamilyUp) ∧
      Nonempty (FieldFaithful EquicontinuousFamilyUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial EquicontinuousFamilyUp) ∧
          (∀ h : BHist,
            equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist h) = h) ∧
            (∀ x : EquicontinuousFamilyUp,
              equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) =
                some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro equicontinuousFamilyChapterTasteGate,
      Nonempty.intro equicontinuousFamilyFieldFaithful,
      Nonempty.intro equicontinuousFamilyNontrivial,
      equicontinuousFamilyDecode_encode_bhist,
      equicontinuousFamily_round_trip⟩

end BEDC.Derived.EquicontinuousFamilyUp
