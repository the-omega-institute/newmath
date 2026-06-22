import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedMonotoneLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedMonotoneLimitUp : Type where
  | mk (S D U W R E H C P N : BHist) : LocatedMonotoneLimitUp
  deriving DecidableEq

def locatedMonotoneLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedMonotoneLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedMonotoneLimitEncodeBHist h

def locatedMonotoneLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedMonotoneLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedMonotoneLimitDecodeBHist tail)

private theorem LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedMonotoneLimitFields : LocatedMonotoneLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedMonotoneLimitUp.mk S D U W R E H C P N => [S, D, U, W, R, E, H, C, P, N]

def locatedMonotoneLimitToEventFlow : LocatedMonotoneLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedMonotoneLimitUp.mk S D U W R E H C P N =>
      [locatedMonotoneLimitEncodeBHist S,
        locatedMonotoneLimitEncodeBHist D,
        locatedMonotoneLimitEncodeBHist U,
        locatedMonotoneLimitEncodeBHist W,
        locatedMonotoneLimitEncodeBHist R,
        locatedMonotoneLimitEncodeBHist E,
        locatedMonotoneLimitEncodeBHist H,
        locatedMonotoneLimitEncodeBHist C,
        locatedMonotoneLimitEncodeBHist P,
        locatedMonotoneLimitEncodeBHist N]

def locatedMonotoneLimitFromEventFlow : EventFlow → Option LocatedMonotoneLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restD =>
      match restD with
      | [] => none
      | D :: restU =>
          match restU with
          | [] => none
          | U :: restW =>
              match restW with
              | [] => none
              | W :: restR =>
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
                                                (LocatedMonotoneLimitUp.mk
                                                  (locatedMonotoneLimitDecodeBHist S)
                                                  (locatedMonotoneLimitDecodeBHist D)
                                                  (locatedMonotoneLimitDecodeBHist U)
                                                  (locatedMonotoneLimitDecodeBHist W)
                                                  (locatedMonotoneLimitDecodeBHist R)
                                                  (locatedMonotoneLimitDecodeBHist E)
                                                  (locatedMonotoneLimitDecodeBHist H)
                                                  (locatedMonotoneLimitDecodeBHist C)
                                                  (locatedMonotoneLimitDecodeBHist P)
                                                  (locatedMonotoneLimitDecodeBHist N))
                                          | _ :: _ => none

private theorem LocatedMonotoneLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedMonotoneLimitUp,
      locatedMonotoneLimitFromEventFlow (locatedMonotoneLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D U W R E H C P N =>
      change
        some
          (LocatedMonotoneLimitUp.mk
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist S))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist D))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist U))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist W))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist R))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist E))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist H))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist C))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist P))
            (locatedMonotoneLimitDecodeBHist (locatedMonotoneLimitEncodeBHist N))) =
          some (LocatedMonotoneLimitUp.mk S D U W R E H C P N)
      rw [LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode S,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode D,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode U,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode W,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode R,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode E,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode H,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode C,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode P,
        LocatedMonotoneLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem locatedMonotoneLimitToEventFlow_injective {x y : LocatedMonotoneLimitUp} :
    locatedMonotoneLimitToEventFlow x = locatedMonotoneLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedMonotoneLimitFromEventFlow (locatedMonotoneLimitToEventFlow x) =
        locatedMonotoneLimitFromEventFlow (locatedMonotoneLimitToEventFlow y) :=
    congrArg locatedMonotoneLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedMonotoneLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedMonotoneLimitTasteGate_single_carrier_alignment_round_trip y)))

instance locatedMonotoneLimitBHistCarrier : BHistCarrier LocatedMonotoneLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedMonotoneLimitToEventFlow
  fromEventFlow := locatedMonotoneLimitFromEventFlow

instance locatedMonotoneLimitChapterTasteGate : ChapterTasteGate LocatedMonotoneLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedMonotoneLimitFromEventFlow (locatedMonotoneLimitToEventFlow x) = some x
    exact LocatedMonotoneLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedMonotoneLimitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedMonotoneLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedMonotoneLimitChapterTasteGate

theorem LocatedMonotoneLimitTasteGate_single_carrier_alignment :
    (∀ x : LocatedMonotoneLimitUp,
        locatedMonotoneLimitFromEventFlow (locatedMonotoneLimitToEventFlow x) = some x) ∧
      (∀ x y : LocatedMonotoneLimitUp,
        locatedMonotoneLimitToEventFlow x = locatedMonotoneLimitToEventFlow y → x = y) ∧
        locatedMonotoneLimitFields
            (LocatedMonotoneLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedMonotoneLimitTasteGate_single_carrier_alignment_round_trip,
      ⟨fun _ _ heq => locatedMonotoneLimitToEventFlow_injective heq, rfl⟩⟩

end BEDC.Derived.LocatedMonotoneLimitUp
