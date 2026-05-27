import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DugundjiExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DugundjiExtensionUp : Type where
  | mk (A S V T L G R H C P N : BHist) : DugundjiExtensionUp

def dugundjiExtensionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dugundjiExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dugundjiExtensionEncodeBHist h

def dugundjiExtensionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dugundjiExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dugundjiExtensionDecodeBHist tail)

private theorem DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dugundjiExtensionFields : DugundjiExtensionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DugundjiExtensionUp.mk A S V T L G R H C P N => [A, S, V, T, L, G, R, H, C, P, N]

def dugundjiExtensionToEventFlow : DugundjiExtensionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dugundjiExtensionFields x).map dugundjiExtensionEncodeBHist

def dugundjiExtensionFromEventFlow : EventFlow -> Option DugundjiExtensionUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: restA =>
      match restA with
      | S :: restS =>
          match restS with
          | V :: restV =>
              match restV with
              | T :: restT =>
                  match restT with
                  | L :: restL =>
                      match restL with
                      | G :: restG =>
                          match restG with
                          | R :: restR =>
                              match restR with
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
                                                    (DugundjiExtensionUp.mk
                                                      (dugundjiExtensionDecodeBHist A)
                                                      (dugundjiExtensionDecodeBHist S)
                                                      (dugundjiExtensionDecodeBHist V)
                                                      (dugundjiExtensionDecodeBHist T)
                                                      (dugundjiExtensionDecodeBHist L)
                                                      (dugundjiExtensionDecodeBHist G)
                                                      (dugundjiExtensionDecodeBHist R)
                                                      (dugundjiExtensionDecodeBHist H)
                                                      (dugundjiExtensionDecodeBHist C)
                                                      (dugundjiExtensionDecodeBHist P)
                                                      (dugundjiExtensionDecodeBHist N))
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

private theorem DugundjiExtensionTasteGate_single_carrier_alignment_round_trip :
    forall x : DugundjiExtensionUp,
      dugundjiExtensionFromEventFlow (dugundjiExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S V T L G R H C P N =>
      change
        some
            (DugundjiExtensionUp.mk
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist A))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist S))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist V))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist T))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist L))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist G))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist R))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist H))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist C))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist P))
              (dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist N))) =
          some (DugundjiExtensionUp.mk A S V T L G R H C P N)
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode A]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode S]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode V]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode T]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode L]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode G]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode R]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode H]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode C]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode P]
      rw [DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DugundjiExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DugundjiExtensionUp} :
    dugundjiExtensionToEventFlow x = dugundjiExtensionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dugundjiExtensionFromEventFlow (dugundjiExtensionToEventFlow x) =
        dugundjiExtensionFromEventFlow (dugundjiExtensionToEventFlow y) :=
    congrArg dugundjiExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DugundjiExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DugundjiExtensionTasteGate_single_carrier_alignment_round_trip y)))

instance dugundjiExtensionBHistCarrier : BHistCarrier DugundjiExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dugundjiExtensionToEventFlow
  fromEventFlow := dugundjiExtensionFromEventFlow

instance dugundjiExtensionChapterTasteGate : ChapterTasteGate DugundjiExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dugundjiExtensionFromEventFlow (dugundjiExtensionToEventFlow x) = some x
    exact DugundjiExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DugundjiExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DugundjiExtensionTasteGate_single_carrier_alignment :
    (forall h : BHist, dugundjiExtensionDecodeBHist (dugundjiExtensionEncodeBHist h) = h) ∧
      (forall x : DugundjiExtensionUp,
        dugundjiExtensionFromEventFlow (dugundjiExtensionToEventFlow x) = some x) ∧
      (forall x y : DugundjiExtensionUp,
        dugundjiExtensionToEventFlow x = dugundjiExtensionToEventFlow y -> x = y) ∧
      dugundjiExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DugundjiExtensionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact DugundjiExtensionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact DugundjiExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.DugundjiExtensionUp
