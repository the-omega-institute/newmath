import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArzelaAscoliFiniteModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArzelaAscoliFiniteModulusUp : Type where
  | mk (K F M W R E H C P N : BHist) : ArzelaAscoliFiniteModulusUp
  deriving DecidableEq

def ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist h

def ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields :
    ArzelaAscoliFiniteModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArzelaAscoliFiniteModulusUp.mk K F M W R E H C P N =>
      [K, F, M, W, R, E, H, C, P, N]

def ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow :
    ArzelaAscoliFiniteModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields x).map
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist

private def ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault index rest

def ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option ArzelaAscoliFiniteModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ArzelaAscoliFiniteModulusUp.mk
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArzelaAscoliFiniteModulusUp,
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M W R E H C P N =>
      change
        some
          (ArzelaAscoliFiniteModulusUp.mk
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist K))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist F))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist M))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist W))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist R))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist E))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist H))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist C))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist P))
            (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decodeBHist
              (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ArzelaAscoliFiniteModulusUp.mk K F M W R E H C P N)
      rw [ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode K,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode F,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode M,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode W,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode R,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode E,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode H,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode C,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode P,
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArzelaAscoliFiniteModulusUp} :
    ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow x =
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow x) =
        ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow
          (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ArzelaAscoliFiniteModulusUp,
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields x =
          ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ M₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ M₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hF tail1
          injection tail1 with hM tail2
          injection tail2 with hW tail3
          injection tail3 with hR tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hK
          subst hF
          subst hM
          subst hW
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance arzelaAscoliFiniteModulusBHistCarrier :
    BHistCarrier ArzelaAscoliFiniteModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow

instance arzelaAscoliFiniteModulusChapterTasteGate :
    ChapterTasteGate ArzelaAscoliFiniteModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fromEventFlow
        (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance arzelaAscoliFiniteModulusFieldFaithful :
    FieldFaithful ArzelaAscoliFiniteModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields
  field_faithful := ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment_fields_faithful

theorem ArzelaAscoliFiniteModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ArzelaAscoliFiniteModulusUp) ∧
      Nonempty (ChapterTasteGate ArzelaAscoliFiniteModulusUp) ∧
        Nonempty (FieldFaithful ArzelaAscoliFiniteModulusUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨arzelaAscoliFiniteModulusBHistCarrier⟩,
      ⟨arzelaAscoliFiniteModulusChapterTasteGate⟩,
      ⟨arzelaAscoliFiniteModulusFieldFaithful⟩⟩

end BEDC.Derived.ArzelaAscoliFiniteModulusUp
