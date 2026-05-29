import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntervalPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntervalPartitionUp : Type where
  | mk (J M Q D S R E H C P N : BHist) : LocatedRealIntervalPartitionUp
  deriving DecidableEq

def locatedRealIntervalPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntervalPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntervalPartitionEncodeBHist h

def locatedRealIntervalPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntervalPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntervalPartitionDecodeBHist tail)

private theorem LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealIntervalPartitionDecodeBHist
          (locatedRealIntervalPartitionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealIntervalPartitionFields :
    LocatedRealIntervalPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntervalPartitionUp.mk J M Q D S R E H C P N =>
      [J, M, Q, D, S, R, E, H, C, P, N]

def locatedRealIntervalPartitionToEventFlow :
    LocatedRealIntervalPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map locatedRealIntervalPartitionEncodeBHist
        (locatedRealIntervalPartitionFields x)

def locatedRealIntervalPartitionFromEventFlow :
    EventFlow → Option LocatedRealIntervalPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | J :: restJ =>
      match restJ with
      | [] => none
      | M :: restM =>
          match restM with
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
                                                    (LocatedRealIntervalPartitionUp.mk
                                                      (locatedRealIntervalPartitionDecodeBHist J)
                                                      (locatedRealIntervalPartitionDecodeBHist M)
                                                      (locatedRealIntervalPartitionDecodeBHist Q)
                                                      (locatedRealIntervalPartitionDecodeBHist D)
                                                      (locatedRealIntervalPartitionDecodeBHist S)
                                                      (locatedRealIntervalPartitionDecodeBHist R)
                                                      (locatedRealIntervalPartitionDecodeBHist E)
                                                      (locatedRealIntervalPartitionDecodeBHist H)
                                                      (locatedRealIntervalPartitionDecodeBHist C)
                                                      (locatedRealIntervalPartitionDecodeBHist P)
                                                      (locatedRealIntervalPartitionDecodeBHist N))
                                              | _ :: _ => none

private theorem LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealIntervalPartitionUp,
      locatedRealIntervalPartitionFromEventFlow
          (locatedRealIntervalPartitionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J M Q D S R E H C P N =>
      change
        some
          (LocatedRealIntervalPartitionUp.mk
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist J))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist M))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist Q))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist D))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist S))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist R))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist E))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist H))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist C))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist P))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist N))) =
          some (LocatedRealIntervalPartitionUp.mk J M Q D S R E H C P N)
      rw [LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode J,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode M,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode Q,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode D,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode S,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode R,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode E,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode H,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode C,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode P,
        LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode N]

private theorem LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_injective
    {x y : LocatedRealIntervalPartitionUp} :
    locatedRealIntervalPartitionToEventFlow x =
        locatedRealIntervalPartitionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealIntervalPartitionFromEventFlow
          (locatedRealIntervalPartitionToEventFlow x) =
        locatedRealIntervalPartitionFromEventFlow
          (locatedRealIntervalPartitionToEventFlow y) :=
    congrArg locatedRealIntervalPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_round_trip y)))

instance locatedRealIntervalPartitionBHistCarrier :
    BHistCarrier LocatedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealIntervalPartitionToEventFlow
  fromEventFlow := locatedRealIntervalPartitionFromEventFlow

instance locatedRealIntervalPartitionChapterTasteGate :
    ChapterTasteGate LocatedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealIntervalPartitionFromEventFlow
          (locatedRealIntervalPartitionToEventFlow x) =
        some x
    exact LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate LocatedRealIntervalPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealIntervalPartitionChapterTasteGate

theorem LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedRealIntervalPartitionUp) ∧
      (∀ h : BHist,
        locatedRealIntervalPartitionDecodeBHist
            (locatedRealIntervalPartitionEncodeBHist h) =
          h) ∧
        locatedRealIntervalPartitionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro locatedRealIntervalPartitionChapterTasteGate,
      LocatedRealIntervalPartitionUpTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.LocatedRealIntervalPartitionUp
