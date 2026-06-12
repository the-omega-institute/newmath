import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentiallyCompleteUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentiallyCompleteUniformSpaceUp : Type where
  | mk (U S B Q R E H C P N : BHist) : SequentiallyCompleteUniformSpaceUp
  deriving DecidableEq

def sequentiallyCompleteUniformSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentiallyCompleteUniformSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentiallyCompleteUniformSpaceEncodeBHist h

def sequentiallyCompleteUniformSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentiallyCompleteUniformSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentiallyCompleteUniformSpaceDecodeBHist tail)

private theorem sequentiallyCompleteUniformSpaceDecodeEncodeBHist :
    ∀ h : BHist,
      sequentiallyCompleteUniformSpaceDecodeBHist
          (sequentiallyCompleteUniformSpaceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentiallyCompleteUniformSpaceFields :
    SequentiallyCompleteUniformSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentiallyCompleteUniformSpaceUp.mk U S B Q R E H C P N =>
      [U, S, B, Q, R, E, H, C, P, N]

def sequentiallyCompleteUniformSpaceToEventFlow :
    SequentiallyCompleteUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (sequentiallyCompleteUniformSpaceFields x).map
        sequentiallyCompleteUniformSpaceEncodeBHist

def sequentiallyCompleteUniformSpaceFromEventFlow :
    EventFlow → Option SequentiallyCompleteUniformSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: restS =>
      match restS with
      | [] => none
      | S :: restB =>
          match restB with
          | [] => none
          | B :: restQ =>
              match restQ with
              | [] => none
              | Q :: restR =>
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
                                                (SequentiallyCompleteUniformSpaceUp.mk
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist U)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist S)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist B)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist Q)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist R)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist E)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist H)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist C)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist P)
                                                  (sequentiallyCompleteUniformSpaceDecodeBHist N))
                                          | _ :: _ => none

private theorem sequentiallyCompleteUniformSpace_round_trip :
    ∀ x : SequentiallyCompleteUniformSpaceUp,
      sequentiallyCompleteUniformSpaceFromEventFlow
          (sequentiallyCompleteUniformSpaceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U S B Q R E H C P N =>
      change
        some
          (SequentiallyCompleteUniformSpaceUp.mk
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist U))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist S))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist B))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist Q))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist R))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist E))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist H))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist C))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist P))
            (sequentiallyCompleteUniformSpaceDecodeBHist
              (sequentiallyCompleteUniformSpaceEncodeBHist N))) =
          some (SequentiallyCompleteUniformSpaceUp.mk U S B Q R E H C P N)
      rw [sequentiallyCompleteUniformSpaceDecodeEncodeBHist U,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist S,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist B,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist Q,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist R,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist E,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist H,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist C,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist P,
        sequentiallyCompleteUniformSpaceDecodeEncodeBHist N]

private theorem sequentiallyCompleteUniformSpaceToEventFlow_injective
    {x y : SequentiallyCompleteUniformSpaceUp} :
    sequentiallyCompleteUniformSpaceToEventFlow x =
        sequentiallyCompleteUniformSpaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentiallyCompleteUniformSpaceFromEventFlow
          (sequentiallyCompleteUniformSpaceToEventFlow x) =
        sequentiallyCompleteUniformSpaceFromEventFlow
          (sequentiallyCompleteUniformSpaceToEventFlow y) :=
    congrArg sequentiallyCompleteUniformSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentiallyCompleteUniformSpace_round_trip x).symm
      (Eq.trans hread (sequentiallyCompleteUniformSpace_round_trip y)))

instance sequentiallyCompleteUniformSpaceBHistCarrier :
    BHistCarrier SequentiallyCompleteUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentiallyCompleteUniformSpaceToEventFlow
  fromEventFlow := sequentiallyCompleteUniformSpaceFromEventFlow

instance sequentiallyCompleteUniformSpaceChapterTasteGate :
    ChapterTasteGate SequentiallyCompleteUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentiallyCompleteUniformSpaceFromEventFlow
          (sequentiallyCompleteUniformSpaceToEventFlow x) =
        some x
    exact sequentiallyCompleteUniformSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentiallyCompleteUniformSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SequentiallyCompleteUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentiallyCompleteUniformSpaceChapterTasteGate

theorem SequentiallyCompleteUniformSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentiallyCompleteUniformSpaceDecodeBHist
          (sequentiallyCompleteUniformSpaceEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier SequentiallyCompleteUniformSpaceUp) ∧
        Nonempty (ChapterTasteGate SequentiallyCompleteUniformSpaceUp) ∧
          sequentiallyCompleteUniformSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨sequentiallyCompleteUniformSpaceDecodeEncodeBHist,
      ⟨sequentiallyCompleteUniformSpaceBHistCarrier⟩,
      ⟨sequentiallyCompleteUniformSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SequentiallyCompleteUniformSpaceUp
