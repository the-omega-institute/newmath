import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedRealCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedRealCompletionUp : Type where
  | mk (D S R L E H C P N : BHist) : BishopLocatedRealCompletionUp
  deriving DecidableEq

def bishopLocatedRealCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedRealCompletionEncodeBHist h

def bishopLocatedRealCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedRealCompletionDecodeBHist tail)

private theorem BishopLocatedRealCompletion_decode_encode :
    forall h : BHist,
      bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedRealCompletionFields : BishopLocatedRealCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedRealCompletionUp.mk D S R L E H C P N => [D, S, R, L, E, H, C, P, N]

def bishopLocatedRealCompletionToEventFlow : BishopLocatedRealCompletionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopLocatedRealCompletionFields x).map bishopLocatedRealCompletionEncodeBHist

private def bishopLocatedRealCompletionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedRealCompletionEventAtDefault index rest

def bishopLocatedRealCompletionFromEventFlow :
    EventFlow -> Option BishopLocatedRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopLocatedRealCompletionUp.mk
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 0 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 1 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 2 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 3 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 4 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 5 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 6 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 7 ef))
        (bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEventAtDefault 8 ef)))

private theorem BishopLocatedRealCompletion_round_trip :
    forall x : BishopLocatedRealCompletionUp,
      bishopLocatedRealCompletionFromEventFlow
          (bishopLocatedRealCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R L E H C P N =>
      change
        some
            (BishopLocatedRealCompletionUp.mk
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist D))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist S))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist R))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist L))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist E))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist H))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist C))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist P))
              (bishopLocatedRealCompletionDecodeBHist
                (bishopLocatedRealCompletionEncodeBHist N))) =
          some (BishopLocatedRealCompletionUp.mk D S R L E H C P N)
      rw [BishopLocatedRealCompletion_decode_encode D,
        BishopLocatedRealCompletion_decode_encode S,
        BishopLocatedRealCompletion_decode_encode R,
        BishopLocatedRealCompletion_decode_encode L,
        BishopLocatedRealCompletion_decode_encode E,
        BishopLocatedRealCompletion_decode_encode H,
        BishopLocatedRealCompletion_decode_encode C,
        BishopLocatedRealCompletion_decode_encode P,
        BishopLocatedRealCompletion_decode_encode N]

private theorem BishopLocatedRealCompletion_toEventFlow_injective
    {x y : BishopLocatedRealCompletionUp} :
    bishopLocatedRealCompletionToEventFlow x =
        bishopLocatedRealCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedRealCompletionFromEventFlow (bishopLocatedRealCompletionToEventFlow x) =
        bishopLocatedRealCompletionFromEventFlow (bishopLocatedRealCompletionToEventFlow y) :=
    congrArg bishopLocatedRealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedRealCompletion_round_trip x).symm
      (Eq.trans hread (BishopLocatedRealCompletion_round_trip y)))

private theorem BishopLocatedRealCompletion_fields_faithful :
    forall x y : BishopLocatedRealCompletionUp,
      bishopLocatedRealCompletionFields x = bishopLocatedRealCompletionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 L2 E2 H2 C2 P2 N2 =>
          injection hfields with hD tail0
          injection tail0 with hS tail1
          injection tail1 with hR tail2
          injection tail2 with hL tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hD
          subst hS
          subst hR
          subst hL
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance bishopLocatedRealCompletionBHistCarrier :
    BHistCarrier BishopLocatedRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedRealCompletionToEventFlow
  fromEventFlow := bishopLocatedRealCompletionFromEventFlow

instance bishopLocatedRealCompletionChapterTasteGate :
    ChapterTasteGate BishopLocatedRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedRealCompletionFromEventFlow (bishopLocatedRealCompletionToEventFlow x) =
        some x
    exact BishopLocatedRealCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedRealCompletion_toEventFlow_injective heq)

instance bishopLocatedRealCompletionFieldFaithful :
    FieldFaithful BishopLocatedRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedRealCompletionFields
  field_faithful := BishopLocatedRealCompletion_fields_faithful

instance bishopLocatedRealCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopLocatedRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedRealCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedRealCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopLocatedRealCompletion_namecert_obligations :
    Nonempty (ChapterTasteGate BishopLocatedRealCompletionUp) ∧
      Nonempty (FieldFaithful BishopLocatedRealCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopLocatedRealCompletionUp) ∧
          (∀ D S R L E H C P N : BHist,
            bishopLocatedRealCompletionFields
                (BishopLocatedRealCompletionUp.mk D S R L E H C P N) =
              [D, S, R, L, E, H, C, P, N]) ∧
            (∀ h : BHist,
              bishopLocatedRealCompletionDecodeBHist
                  (bishopLocatedRealCompletionEncodeBHist h) =
                h) ∧
              bishopLocatedRealCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨bishopLocatedRealCompletionChapterTasteGate⟩,
      ⟨bishopLocatedRealCompletionFieldFaithful⟩,
      ⟨bishopLocatedRealCompletionNontrivial⟩,
      (by
        intro D S R L E H C P N
        rfl),
      BishopLocatedRealCompletion_decode_encode,
      rfl⟩

end BEDC.Derived.BishopLocatedRealCompletionUp
