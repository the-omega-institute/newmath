import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionModulusSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionModulusSelectionUp : Type where
  | mk (M n k W D R E H C P N : BHist) : BishopCompletionModulusSelectionUp
  deriving DecidableEq

def bishopCompletionModulusSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionModulusSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionModulusSelectionEncodeBHist h

def bishopCompletionModulusSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionModulusSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionModulusSelectionDecodeBHist tail)

private theorem BishopCompletionModulusSelection_decode_encode :
    ∀ h : BHist,
      bishopCompletionModulusSelectionDecodeBHist
        (bishopCompletionModulusSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionModulusSelectionFields :
    BishopCompletionModulusSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionModulusSelectionUp.mk M n k W D R E H C P N =>
      [M, n, k, W, D, R, E, H, C, P, N]

def bishopCompletionModulusSelectionToEventFlow :
    BishopCompletionModulusSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map bishopCompletionModulusSelectionEncodeBHist
        (bishopCompletionModulusSelectionFields x)

private def bishopCompletionModulusSelectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionModulusSelectionEventAt index rest

def bishopCompletionModulusSelectionFromEventFlow :
    EventFlow → Option BishopCompletionModulusSelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopCompletionModulusSelectionUp.mk
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 0 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 1 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 2 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 3 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 4 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 5 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 6 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 7 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 8 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 9 ef))
          (bishopCompletionModulusSelectionDecodeBHist
            (bishopCompletionModulusSelectionEventAt 10 ef)))

private theorem BishopCompletionModulusSelection_round_trip :
    ∀ x : BishopCompletionModulusSelectionUp,
      bishopCompletionModulusSelectionFromEventFlow
        (bishopCompletionModulusSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M n k W D R E H C P N =>
      change
        some
          (BishopCompletionModulusSelectionUp.mk
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist M))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist n))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist k))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist W))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist D))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist R))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist E))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist H))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist C))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist P))
            (bishopCompletionModulusSelectionDecodeBHist
              (bishopCompletionModulusSelectionEncodeBHist N))) =
          some (BishopCompletionModulusSelectionUp.mk M n k W D R E H C P N)
      rw [BishopCompletionModulusSelection_decode_encode M,
        BishopCompletionModulusSelection_decode_encode n,
        BishopCompletionModulusSelection_decode_encode k,
        BishopCompletionModulusSelection_decode_encode W,
        BishopCompletionModulusSelection_decode_encode D,
        BishopCompletionModulusSelection_decode_encode R,
        BishopCompletionModulusSelection_decode_encode E,
        BishopCompletionModulusSelection_decode_encode H,
        BishopCompletionModulusSelection_decode_encode C,
        BishopCompletionModulusSelection_decode_encode P,
        BishopCompletionModulusSelection_decode_encode N]

private theorem BishopCompletionModulusSelectionToEventFlow_injective
    {x y : BishopCompletionModulusSelectionUp} :
    bishopCompletionModulusSelectionToEventFlow x =
      bishopCompletionModulusSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionModulusSelectionFromEventFlow
          (bishopCompletionModulusSelectionToEventFlow x) =
        bishopCompletionModulusSelectionFromEventFlow
          (bishopCompletionModulusSelectionToEventFlow y) :=
    congrArg bishopCompletionModulusSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompletionModulusSelection_round_trip x).symm
      (Eq.trans hread (BishopCompletionModulusSelection_round_trip y)))

private theorem BishopCompletionModulusSelection_fields_injective :
    ∀ x y : BishopCompletionModulusSelectionUp,
      bishopCompletionModulusSelectionFields x =
        bishopCompletionModulusSelectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 n1 k1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 n2 k2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCompletionModulusSelectionBHistCarrier :
    BHistCarrier BishopCompletionModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionModulusSelectionToEventFlow
  fromEventFlow := bishopCompletionModulusSelectionFromEventFlow

instance bishopCompletionModulusSelectionChapterTasteGate :
    ChapterTasteGate BishopCompletionModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionModulusSelectionFromEventFlow
        (bishopCompletionModulusSelectionToEventFlow x) = some x
    exact BishopCompletionModulusSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCompletionModulusSelectionToEventFlow_injective heq)

instance bishopCompletionModulusSelectionFieldFaithful :
    FieldFaithful BishopCompletionModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompletionModulusSelectionFields
  field_faithful := BishopCompletionModulusSelection_fields_injective

instance bishopCompletionModulusSelectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopCompletionModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompletionModulusSelectionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BishopCompletionModulusSelectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopCompletionModulusSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompletionModulusSelectionChapterTasteGate

end BEDC.Derived.BishopCompletionModulusSelectionUp
