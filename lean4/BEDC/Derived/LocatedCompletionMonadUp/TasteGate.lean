import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionMonadUp : Type where
  | mk (L M U J S R D E H C P N : BHist) : LocatedCompletionMonadUp
  deriving DecidableEq

def locatedCompletionMonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionMonadEncodeBHist h

def locatedCompletionMonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionMonadDecodeBHist tail)

private theorem LocatedCompletionMonadTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionMonadToEventFlow : LocatedCompletionMonadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionMonadUp.mk L M U J S R D E H C P N =>
      [locatedCompletionMonadEncodeBHist L,
        locatedCompletionMonadEncodeBHist M,
        locatedCompletionMonadEncodeBHist U,
        locatedCompletionMonadEncodeBHist J,
        locatedCompletionMonadEncodeBHist S,
        locatedCompletionMonadEncodeBHist R,
        locatedCompletionMonadEncodeBHist D,
        locatedCompletionMonadEncodeBHist E,
        locatedCompletionMonadEncodeBHist H,
        locatedCompletionMonadEncodeBHist C,
        locatedCompletionMonadEncodeBHist P,
        locatedCompletionMonadEncodeBHist N]

def locatedCompletionMonadFromEventFlow : EventFlow → Option LocatedCompletionMonadUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restM =>
      match restM with
      | [] => none
      | M :: restU =>
          match restU with
          | [] => none
          | U :: restJ =>
              match restJ with
              | [] => none
              | J :: restS =>
                  match restS with
                  | [] => none
                  | S :: restR =>
                      match restR with
                      | [] => none
                      | R :: restD =>
                          match restD with
                          | [] => none
                          | D :: restE =>
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
                                                        (LocatedCompletionMonadUp.mk
                                                          (locatedCompletionMonadDecodeBHist L)
                                                          (locatedCompletionMonadDecodeBHist M)
                                                          (locatedCompletionMonadDecodeBHist U)
                                                          (locatedCompletionMonadDecodeBHist J)
                                                          (locatedCompletionMonadDecodeBHist S)
                                                          (locatedCompletionMonadDecodeBHist R)
                                                          (locatedCompletionMonadDecodeBHist D)
                                                          (locatedCompletionMonadDecodeBHist E)
                                                          (locatedCompletionMonadDecodeBHist H)
                                                          (locatedCompletionMonadDecodeBHist C)
                                                          (locatedCompletionMonadDecodeBHist P)
                                                          (locatedCompletionMonadDecodeBHist N))
                                                  | _ :: _ => none

private theorem LocatedCompletionMonadTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompletionMonadUp,
      locatedCompletionMonadFromEventFlow (locatedCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk L M U J S R D E H C P N =>
      change
        some
          (LocatedCompletionMonadUp.mk
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist L))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist M))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist U))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist J))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist S))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist R))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist D))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist E))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist H))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist C))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist P))
            (locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist N))) =
          some (LocatedCompletionMonadUp.mk L M U J S R D E H C P N)
      rw [LocatedCompletionMonadTasteGate_single_carrier_alignment_decode L,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode M,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode U,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode J,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode S,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode R,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode D,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode E,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode H,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode C,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode P,
        LocatedCompletionMonadTasteGate_single_carrier_alignment_decode N]

theorem LocatedCompletionMonadTasteGate_single_carrier_alignment_injective
    {x y : LocatedCompletionMonadUp} :
    locatedCompletionMonadToEventFlow x = locatedCompletionMonadToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionMonadFromEventFlow (locatedCompletionMonadToEventFlow x) =
        locatedCompletionMonadFromEventFlow (locatedCompletionMonadToEventFlow y) :=
    congrArg locatedCompletionMonadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCompletionMonadTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompletionMonadTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompletionMonadBHistCarrier : BHistCarrier LocatedCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionMonadToEventFlow
  fromEventFlow := locatedCompletionMonadFromEventFlow

instance locatedCompletionMonadChapterTasteGate : ChapterTasteGate LocatedCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCompletionMonadFromEventFlow (locatedCompletionMonadToEventFlow x) = some x
    exact LocatedCompletionMonadTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompletionMonadTasteGate_single_carrier_alignment_injective heq)

theorem LocatedCompletionMonadTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCompletionMonadDecodeBHist (locatedCompletionMonadEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionMonadUp,
        locatedCompletionMonadFromEventFlow (locatedCompletionMonadToEventFlow x) = some x) ∧
        (∀ x y : LocatedCompletionMonadUp,
          locatedCompletionMonadToEventFlow x = locatedCompletionMonadToEventFlow y → x = y) ∧
          locatedCompletionMonadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedCompletionMonadTasteGate_single_carrier_alignment_decode
  · constructor
    · exact LocatedCompletionMonadTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact LocatedCompletionMonadTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.LocatedCompletionMonadUp
