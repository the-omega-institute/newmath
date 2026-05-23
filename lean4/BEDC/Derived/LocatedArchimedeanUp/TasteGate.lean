import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedArchimedeanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedArchimedeanUp : Type where
  | mk (L I A D S R E H C P N : BHist) : LocatedArchimedeanUp
  deriving DecidableEq

def locatedArchimedeanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedArchimedeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedArchimedeanEncodeBHist h

def locatedArchimedeanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedArchimedeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedArchimedeanDecodeBHist tail)

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedArchimedeanFields : LocatedArchimedeanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedArchimedeanUp.mk L I A D S R E H C P N => [L, I, A, D, S, R, E, H, C, P, N]

def locatedArchimedeanToEventFlow : LocatedArchimedeanUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedArchimedeanFields x).map locatedArchimedeanEncodeBHist

def locatedArchimedeanFromEventFlow : EventFlow → Option LocatedArchimedeanUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: restL =>
      match restL with
      | I :: restI =>
          match restI with
          | A :: restA =>
              match restA with
              | D :: restD =>
                  match restD with
                  | S :: restS =>
                      match restS with
                      | R :: restR =>
                          match restR with
                          | E :: restE =>
                              match restE with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (LocatedArchimedeanUp.mk
                                                      (locatedArchimedeanDecodeBHist L)
                                                      (locatedArchimedeanDecodeBHist I)
                                                      (locatedArchimedeanDecodeBHist A)
                                                      (locatedArchimedeanDecodeBHist D)
                                                      (locatedArchimedeanDecodeBHist S)
                                                      (locatedArchimedeanDecodeBHist R)
                                                      (locatedArchimedeanDecodeBHist E)
                                                      (locatedArchimedeanDecodeBHist H)
                                                      (locatedArchimedeanDecodeBHist C)
                                                      (locatedArchimedeanDecodeBHist P)
                                                      (locatedArchimedeanDecodeBHist N))
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

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedArchimedeanUp,
      locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L I A D S R E H C P N =>
      change
        some
          (LocatedArchimedeanUp.mk
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist L))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist I))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist A))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist D))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist S))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist R))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist E))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist H))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist C))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist P))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist N))) =
          some (LocatedArchimedeanUp.mk L I A D S R E H C P N)
      rw [LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode L,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode I,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode A,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode D,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode S,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode R,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode E,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode H,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode C,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode P,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedArchimedeanUp} :
    locatedArchimedeanToEventFlow x = locatedArchimedeanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) =
        locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow y) :=
    congrArg locatedArchimedeanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip y)))

instance locatedArchimedeanBHistCarrier : BHistCarrier LocatedArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedArchimedeanToEventFlow
  fromEventFlow := locatedArchimedeanFromEventFlow

instance locatedArchimedeanChapterTasteGate : ChapterTasteGate LocatedArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) = some x
    exact LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedArchimedeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedArchimedeanChapterTasteGate

theorem LocatedArchimedeanTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist h) = h) ∧
      (∀ x : LocatedArchimedeanUp,
        locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) = some x) ∧
      (∀ x y : LocatedArchimedeanUp,
        locatedArchimedeanToEventFlow x = locatedArchimedeanToEventFlow y → x = y) ∧
      locatedArchimedeanEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact LocatedArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.LocatedArchimedeanUp
