import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopUniformCompletionTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopUniformCompletionTheoremUp : Type where
  | mk (X F S R E V H C P N : BHist) : BishopUniformCompletionTheoremUp
  deriving DecidableEq

def bishopUniformCompletionTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopUniformCompletionTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopUniformCompletionTheoremEncodeBHist h

def bishopUniformCompletionTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopUniformCompletionTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopUniformCompletionTheoremDecodeBHist tail)

private theorem bishopUniformCompletionTheorem_decode_encode_bhist :
    ∀ h : BHist,
      bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopUniformCompletionTheoremFields :
    BishopUniformCompletionTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopUniformCompletionTheoremUp.mk X F S R E V H C P N =>
      [X, F, S, R, E, V, H, C, P, N]

def bishopUniformCompletionTheoremToEventFlow :
    BishopUniformCompletionTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopUniformCompletionTheoremFields x).map
      bishopUniformCompletionTheoremEncodeBHist

private def bishopUniformCompletionTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopUniformCompletionTheoremEventAt index rest

def bishopUniformCompletionTheoremFromEventFlow :
    EventFlow → Option BishopUniformCompletionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (BishopUniformCompletionTheoremUp.mk
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 0 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 1 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 2 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 3 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 4 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 5 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 6 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 7 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 8 flow))
        (bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEventAt 9 flow)))

private theorem bishopUniformCompletionTheorem_round_trip :
    ∀ x : BishopUniformCompletionTheoremUp,
      bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F S R E V H C P N =>
      change
        some
            (BishopUniformCompletionTheoremUp.mk
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist X))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist F))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist S))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist R))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist E))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist V))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist H))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist C))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist P))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist N))) =
          some (BishopUniformCompletionTheoremUp.mk X F S R E V H C P N)
      rw [bishopUniformCompletionTheorem_decode_encode_bhist X,
        bishopUniformCompletionTheorem_decode_encode_bhist F,
        bishopUniformCompletionTheorem_decode_encode_bhist S,
        bishopUniformCompletionTheorem_decode_encode_bhist R,
        bishopUniformCompletionTheorem_decode_encode_bhist E,
        bishopUniformCompletionTheorem_decode_encode_bhist V,
        bishopUniformCompletionTheorem_decode_encode_bhist H,
        bishopUniformCompletionTheorem_decode_encode_bhist C,
        bishopUniformCompletionTheorem_decode_encode_bhist P,
        bishopUniformCompletionTheorem_decode_encode_bhist N]

private theorem bishopUniformCompletionTheoremToEventFlow_injective
    {x y : BishopUniformCompletionTheoremUp} :
    bishopUniformCompletionTheoremToEventFlow x =
        bishopUniformCompletionTheoremToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow x) =
        bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow y) :=
    congrArg bishopUniformCompletionTheoremFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (bishopUniformCompletionTheorem_round_trip x).symm
      (Eq.trans hread (bishopUniformCompletionTheorem_round_trip y)))

private theorem bishopUniformCompletionTheorem_field_faithful :
    ∀ x y : BishopUniformCompletionTheoremUp,
      bishopUniformCompletionTheoremFields x =
          bishopUniformCompletionTheoremFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 S1 R1 E1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 S2 R2 E2 V2 H2 C2 P2 N2 =>
          injection hfields with hX tail0
          injection tail0 with hF tail1
          injection tail1 with hS tail2
          injection tail2 with hR tail3
          injection tail3 with hE tail4
          injection tail4 with hV tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hX
          subst hF
          subst hS
          subst hR
          subst hE
          subst hV
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance bishopUniformCompletionTheoremBHistCarrier :
    BHistCarrier BishopUniformCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopUniformCompletionTheoremToEventFlow
  fromEventFlow := bishopUniformCompletionTheoremFromEventFlow

instance bishopUniformCompletionTheoremChapterTasteGate :
    ChapterTasteGate BishopUniformCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow x) =
        some x
    exact bishopUniformCompletionTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopUniformCompletionTheoremToEventFlow_injective heq)

instance bishopUniformCompletionTheoremFieldFaithful :
    FieldFaithful BishopUniformCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopUniformCompletionTheoremFields
  field_faithful := bishopUniformCompletionTheorem_field_faithful

instance bishopUniformCompletionTheoremNontrivial :
    Nontrivial BishopUniformCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopUniformCompletionTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BishopUniformCompletionTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopUniformCompletionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopUniformCompletionTheoremChapterTasteGate

theorem BishopUniformCompletionTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEncodeBHist h) =
        h) ∧
      (∀ x : BishopUniformCompletionTheoremUp,
        bishopUniformCompletionTheoremFromEventFlow
            (bishopUniformCompletionTheoremToEventFlow x) =
          some x) ∧
        (∀ x y : BishopUniformCompletionTheoremUp,
          bishopUniformCompletionTheoremToEventFlow x =
              bishopUniformCompletionTheoremToEventFlow y →
            x = y) ∧
          Nonempty (ChapterTasteGate BishopUniformCompletionTheoremUp) ∧
            Nonempty (FieldFaithful BishopUniformCompletionTheoremUp) ∧
              Nonempty (Nontrivial BishopUniformCompletionTheoremUp) ∧
                bishopUniformCompletionTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bishopUniformCompletionTheorem_decode_encode_bhist,
      bishopUniformCompletionTheorem_round_trip,
      fun _ _ hxy => bishopUniformCompletionTheoremToEventFlow_injective hxy,
      ⟨bishopUniformCompletionTheoremChapterTasteGate⟩,
      ⟨bishopUniformCompletionTheoremFieldFaithful⟩,
      ⟨bishopUniformCompletionTheoremNontrivial⟩,
      rfl⟩

end BEDC.Derived.BishopUniformCompletionTheoremUp
