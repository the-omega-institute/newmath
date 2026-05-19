import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StopCodonZeckendorfSuffixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StopCodonZeckendorfSuffixUp : Type where
  | mk : (A W S F L T B H C P N : BHist) → StopCodonZeckendorfSuffixUp
  deriving DecidableEq

def StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist h

def StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields :
    StopCodonZeckendorfSuffixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StopCodonZeckendorfSuffixUp.mk A W S F L T B H C P N =>
      [A, W, S, F, L, T, B, H, C, P, N]

def StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow :
    StopCodonZeckendorfSuffixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields x).map
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist

def StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option StopCodonZeckendorfSuffixUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: W :: S :: F :: L :: T :: B :: H :: C :: P :: N :: [] =>
      some
        (StopCodonZeckendorfSuffixUp.mk
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist A)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist W)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist S)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist F)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist L)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist T)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist B)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist H)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist C)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist P)
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StopCodonZeckendorfSuffixUp,
      StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W S F L T B H C P N =>
      change
        some
          (StopCodonZeckendorfSuffixUp.mk
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist A))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist W))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist S))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist F))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist L))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist T))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist B))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist H))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist C))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist P))
            (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decodeBHist
              (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (StopCodonZeckendorfSuffixUp.mk A W S F L T B H C P N)
      rw [StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode A,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode W,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode S,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode F,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode L,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode T,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode B,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode H,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode C,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode P,
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_decode_encode N]

private theorem StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StopCodonZeckendorfSuffixUp} :
    StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow x =
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow x) =
        StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_round_trip y)))

private theorem StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : StopCodonZeckendorfSuffixUp,
      StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields x =
          StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ W₁ S₁ F₁ L₁ T₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ W₂ S₂ F₂ L₂ T₂ B₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA tail0
          injection tail0 with hW tail1
          injection tail1 with hS tail2
          injection tail2 with hF tail3
          injection tail3 with hL tail4
          injection tail4 with hT tail5
          injection tail5 with hB tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hA
          subst hW
          subst hS
          subst hF
          subst hL
          subst hT
          subst hB
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance stopCodonZeckendorfSuffixBHistCarrier :
    BHistCarrier StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow

instance stopCodonZeckendorfSuffixChapterTasteGate :
    ChapterTasteGate StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fromEventFlow
          (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance stopCodonZeckendorfSuffixFieldFaithful :
    FieldFaithful StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields
  field_faithful := StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields_faithful

instance stopCodonZeckendorfSuffixNontrivial :
    Nontrivial StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StopCodonZeckendorfSuffixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StopCodonZeckendorfSuffixUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment
    (A W S F L T B H C P N : BHist) :
    StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment_fields
        (StopCodonZeckendorfSuffixUp.mk A W S F L T B H C P N) =
      [A, W, S, F, L, T, B, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  rfl

end BEDC.Derived.StopCodonZeckendorfSuffixUp
