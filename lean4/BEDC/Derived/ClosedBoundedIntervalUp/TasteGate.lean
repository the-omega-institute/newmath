import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalUp : Type where
  | mk (L U O Q D S R E H C P N : BHist) : ClosedBoundedIntervalUp
  deriving DecidableEq

def closedBoundedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalEncodeBHist h

def closedBoundedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalDecodeBHist tail)

private theorem ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedBoundedIntervalFields : ClosedBoundedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalUp.mk L U O Q D S R E H C P N => [L, U, O, Q, D, S, R, E, H, C, P, N]

def closedBoundedIntervalToEventFlow : ClosedBoundedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map closedBoundedIntervalEncodeBHist (closedBoundedIntervalFields x)

def closedBoundedIntervalFromEventFlow : EventFlow → Option ClosedBoundedIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restL =>
      match restL with
      | [] => none
      | U :: restU =>
          match restU with
          | [] => none
          | O :: restO =>
              match restO with
              | [] => none
              | Q :: restQ =>
                  match restQ with
                  | [] => none
                  | D :: restD =>
                      match restD with
                      | [] => none
                      | S :: restS =>
                          match restS with
                          | [] => none
                          | R :: restR =>
                              match restR with
                              | [] => none
                              | E :: restE =>
                                  match restE with
                                  | [] => none
                                  | H :: restH =>
                                      match restH with
                                      | [] => none
                                      | C :: restC =>
                                          match restC with
                                          | [] => none
                                          | P :: restP =>
                                              match restP with
                                              | [] => none
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (ClosedBoundedIntervalUp.mk
                                                          (closedBoundedIntervalDecodeBHist L)
                                                          (closedBoundedIntervalDecodeBHist U)
                                                          (closedBoundedIntervalDecodeBHist O)
                                                          (closedBoundedIntervalDecodeBHist Q)
                                                          (closedBoundedIntervalDecodeBHist D)
                                                          (closedBoundedIntervalDecodeBHist S)
                                                          (closedBoundedIntervalDecodeBHist R)
                                                          (closedBoundedIntervalDecodeBHist E)
                                                          (closedBoundedIntervalDecodeBHist H)
                                                          (closedBoundedIntervalDecodeBHist C)
                                                          (closedBoundedIntervalDecodeBHist P)
                                                          (closedBoundedIntervalDecodeBHist N))
                                                  | _ :: _ => none

private theorem ClosedBoundedIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedBoundedIntervalUp,
      closedBoundedIntervalFromEventFlow (closedBoundedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U O Q D S R E H C P N =>
      change
        some
          (ClosedBoundedIntervalUp.mk
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist L))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist U))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist O))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist Q))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist D))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist S))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist R))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist E))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist H))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist C))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist P))
            (closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist N))) =
          some (ClosedBoundedIntervalUp.mk L U O Q D S R E H C P N)
      rw [ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode L,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode U,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode O,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode Q,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode D,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode S,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode R,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode E,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode H,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode C,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode P,
        ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode N]

private theorem ClosedBoundedIntervalTasteGate_single_carrier_alignment_injective
    {x y : ClosedBoundedIntervalUp} :
    closedBoundedIntervalToEventFlow x = closedBoundedIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalFromEventFlow (closedBoundedIntervalToEventFlow x) =
        closedBoundedIntervalFromEventFlow (closedBoundedIntervalToEventFlow y) :=
    congrArg closedBoundedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedBoundedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedBoundedIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance closedBoundedIntervalBHistCarrier : BHistCarrier ClosedBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalToEventFlow
  fromEventFlow := closedBoundedIntervalFromEventFlow

instance closedBoundedIntervalChapterTasteGate : ChapterTasteGate ClosedBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedBoundedIntervalFromEventFlow (closedBoundedIntervalToEventFlow x) = some x
    exact ClosedBoundedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedBoundedIntervalTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate ClosedBoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedBoundedIntervalChapterTasteGate

theorem ClosedBoundedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedBoundedIntervalDecodeBHist (closedBoundedIntervalEncodeBHist h) = h) ∧
      (∀ x : ClosedBoundedIntervalUp,
        closedBoundedIntervalFromEventFlow (closedBoundedIntervalToEventFlow x) = some x) ∧
        (∀ x y : ClosedBoundedIntervalUp,
          closedBoundedIntervalToEventFlow x = closedBoundedIntervalToEventFlow y → x = y) ∧
          closedBoundedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ClosedBoundedIntervalTasteGate_single_carrier_alignment_decode,
      ClosedBoundedIntervalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => ClosedBoundedIntervalTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.ClosedBoundedIntervalUp
