import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionUniversalBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionUniversalBoundaryUp : Type where
  | mk (Q S R D A U E L H C P N : BHist) : BishopCompletionUniversalBoundaryUp
  deriving DecidableEq

def bishopCompletionUniversalBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionUniversalBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionUniversalBoundaryEncodeBHist h

def bishopCompletionUniversalBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionUniversalBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionUniversalBoundaryDecodeBHist tail)

private theorem BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCompletionUniversalBoundaryDecodeBHist
        (bishopCompletionUniversalBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionUniversalBoundaryFields :
    BishopCompletionUniversalBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionUniversalBoundaryUp.mk Q S R D A U E L H C P N =>
      [Q, S, R, D, A, U, E, L, H, C, P, N]

def bishopCompletionUniversalBoundaryToEventFlow :
    BishopCompletionUniversalBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopCompletionUniversalBoundaryFields x).map
        bishopCompletionUniversalBoundaryEncodeBHist

def bishopCompletionUniversalBoundaryFromEventFlow :
    EventFlow → Option BishopCompletionUniversalBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: restQ =>
      match restQ with
      | S :: restS =>
          match restS with
          | R :: restR =>
              match restR with
              | D :: restD =>
                  match restD with
                  | A :: restA =>
                      match restA with
                      | U :: restU =>
                          match restU with
                          | E :: restE =>
                              match restE with
                              | L :: restL =>
                                  match restL with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (BishopCompletionUniversalBoundaryUp.mk
                                                          (bishopCompletionUniversalBoundaryDecodeBHist Q)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist S)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist R)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist D)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist A)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist U)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist E)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist L)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist H)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist C)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist P)
                                                          (bishopCompletionUniversalBoundaryDecodeBHist N))
                                                  | _ :: _ => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCompletionUniversalBoundaryUp,
      bishopCompletionUniversalBoundaryFromEventFlow
        (bishopCompletionUniversalBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S R D A U E L H C P N =>
      change
        some
          (BishopCompletionUniversalBoundaryUp.mk
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist Q))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist S))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist R))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist D))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist A))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist U))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist E))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist L))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist H))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist C))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist P))
            (bishopCompletionUniversalBoundaryDecodeBHist
              (bishopCompletionUniversalBoundaryEncodeBHist N))) =
          some (BishopCompletionUniversalBoundaryUp.mk Q S R D A U E L H C P N)
      rw [BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode Q,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode S,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode R,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode D,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode A,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode U,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode E,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode L,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode H,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode C,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode P,
        BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompletionUniversalBoundaryUp} :
    bishopCompletionUniversalBoundaryToEventFlow x =
      bishopCompletionUniversalBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionUniversalBoundaryFromEventFlow
          (bishopCompletionUniversalBoundaryToEventFlow x) =
        bishopCompletionUniversalBoundaryFromEventFlow
          (bishopCompletionUniversalBoundaryToEventFlow y) :=
    congrArg bishopCompletionUniversalBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCompletionUniversalBoundaryBHistCarrier :
    BHistCarrier BishopCompletionUniversalBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionUniversalBoundaryToEventFlow
  fromEventFlow := bishopCompletionUniversalBoundaryFromEventFlow

instance bishopCompletionUniversalBoundaryChapterTasteGate :
    ChapterTasteGate BishopCompletionUniversalBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionUniversalBoundaryFromEventFlow
        (bishopCompletionUniversalBoundaryToEventFlow x) = some x
    exact BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCompletionUniversalBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompletionUniversalBoundaryChapterTasteGate

theorem BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompletionUniversalBoundaryDecodeBHist
        (bishopCompletionUniversalBoundaryEncodeBHist h) = h) ∧
      (∀ x : BishopCompletionUniversalBoundaryUp,
        bishopCompletionUniversalBoundaryFromEventFlow
          (bishopCompletionUniversalBoundaryToEventFlow x) = some x) ∧
      (∀ x y : BishopCompletionUniversalBoundaryUp,
        bishopCompletionUniversalBoundaryToEventFlow x =
          bishopCompletionUniversalBoundaryToEventFlow y → x = y) ∧
      bishopCompletionUniversalBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_decode
  constructor
  · exact BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact
      BishopCompletionUniversalBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.BishopCompletionUniversalBoundaryUp
