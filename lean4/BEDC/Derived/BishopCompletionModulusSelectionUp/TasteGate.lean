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

private theorem bishopCompletionModulusSelectionDecode_encode :
    ∀ h : BHist,
      bishopCompletionModulusSelectionDecodeBHist
          (bishopCompletionModulusSelectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionModulusSelectionToEventFlow :
    BishopCompletionModulusSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionModulusSelectionUp.mk M n k W D R E H C P N =>
      [bishopCompletionModulusSelectionEncodeBHist M,
        bishopCompletionModulusSelectionEncodeBHist n,
        bishopCompletionModulusSelectionEncodeBHist k,
        bishopCompletionModulusSelectionEncodeBHist W,
        bishopCompletionModulusSelectionEncodeBHist D,
        bishopCompletionModulusSelectionEncodeBHist R,
        bishopCompletionModulusSelectionEncodeBHist E,
        bishopCompletionModulusSelectionEncodeBHist H,
        bishopCompletionModulusSelectionEncodeBHist C,
        bishopCompletionModulusSelectionEncodeBHist P,
        bishopCompletionModulusSelectionEncodeBHist N]

def bishopCompletionModulusSelectionFromEventFlow :
    EventFlow → Option BishopCompletionModulusSelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: restn =>
      match restn with
      | [] => none
      | n :: restk =>
          match restk with
          | [] => none
          | k :: restW =>
              match restW with
              | [] => none
              | W :: restD =>
                  match restD with
                  | [] => none
                  | D :: restR =>
                      match restR with
                      | [] => none
                      | R :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (BishopCompletionModulusSelectionUp.mk
                                                      (bishopCompletionModulusSelectionDecodeBHist M)
                                                      (bishopCompletionModulusSelectionDecodeBHist n)
                                                      (bishopCompletionModulusSelectionDecodeBHist k)
                                                      (bishopCompletionModulusSelectionDecodeBHist W)
                                                      (bishopCompletionModulusSelectionDecodeBHist D)
                                                      (bishopCompletionModulusSelectionDecodeBHist R)
                                                      (bishopCompletionModulusSelectionDecodeBHist E)
                                                      (bishopCompletionModulusSelectionDecodeBHist H)
                                                      (bishopCompletionModulusSelectionDecodeBHist C)
                                                      (bishopCompletionModulusSelectionDecodeBHist P)
                                                      (bishopCompletionModulusSelectionDecodeBHist N))
                                              | _ :: _ => none

private theorem bishopCompletionModulusSelection_round_trip :
    ∀ x : BishopCompletionModulusSelectionUp,
      bishopCompletionModulusSelectionFromEventFlow
          (bishopCompletionModulusSelectionToEventFlow x) =
        some x := by
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
      rw [bishopCompletionModulusSelectionDecode_encode M,
        bishopCompletionModulusSelectionDecode_encode n,
        bishopCompletionModulusSelectionDecode_encode k,
        bishopCompletionModulusSelectionDecode_encode W,
        bishopCompletionModulusSelectionDecode_encode D,
        bishopCompletionModulusSelectionDecode_encode R,
        bishopCompletionModulusSelectionDecode_encode E,
        bishopCompletionModulusSelectionDecode_encode H,
        bishopCompletionModulusSelectionDecode_encode C,
        bishopCompletionModulusSelectionDecode_encode P,
        bishopCompletionModulusSelectionDecode_encode N]

private theorem bishopCompletionModulusSelectionToEventFlow_injective
    {x y : BishopCompletionModulusSelectionUp} :
    bishopCompletionModulusSelectionToEventFlow x =
        bishopCompletionModulusSelectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionModulusSelectionFromEventFlow
          (bishopCompletionModulusSelectionToEventFlow x) =
        bishopCompletionModulusSelectionFromEventFlow
          (bishopCompletionModulusSelectionToEventFlow y) :=
    congrArg bishopCompletionModulusSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompletionModulusSelection_round_trip x).symm
      (Eq.trans hread (bishopCompletionModulusSelection_round_trip y)))

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
          (bishopCompletionModulusSelectionToEventFlow x) =
        some x
    exact bishopCompletionModulusSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompletionModulusSelectionToEventFlow_injective heq)

theorem BishopCompletionModulusSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompletionModulusSelectionDecodeBHist
          (bishopCompletionModulusSelectionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier BishopCompletionModulusSelectionUp) ∧
        Nonempty (ChapterTasteGate BishopCompletionModulusSelectionUp) ∧
          bishopCompletionModulusSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bishopCompletionModulusSelectionDecode_encode,
      ⟨{
        toEventFlow := bishopCompletionModulusSelectionToEventFlow
        fromEventFlow := bishopCompletionModulusSelectionFromEventFlow
      }⟩,
      ⟨{
        round_trip := by
          intro x
          change
            bishopCompletionModulusSelectionFromEventFlow
                (bishopCompletionModulusSelectionToEventFlow x) =
              some x
          exact bishopCompletionModulusSelection_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (bishopCompletionModulusSelectionToEventFlow_injective heq)
      }⟩,
      rfl⟩

end BEDC.Derived.BishopCompletionModulusSelectionUp
