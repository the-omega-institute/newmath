import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalSequenceUp : Type where
  | mk (E W B F Q R H C P N : BHist) : DiagonalSequenceUp
  deriving DecidableEq

def diagonalSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalSequenceEncodeBHist h

def diagonalSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalSequenceDecodeBHist tail)

private theorem DiagonalSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diagonalSequenceToEventFlow : DiagonalSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalSequenceUp.mk E W B F Q R H C P N =>
      [diagonalSequenceEncodeBHist E,
        diagonalSequenceEncodeBHist W,
        diagonalSequenceEncodeBHist B,
        diagonalSequenceEncodeBHist F,
        diagonalSequenceEncodeBHist Q,
        diagonalSequenceEncodeBHist R,
        diagonalSequenceEncodeBHist H,
        diagonalSequenceEncodeBHist C,
        diagonalSequenceEncodeBHist P,
        diagonalSequenceEncodeBHist N]

def diagonalSequenceFromEventFlow : EventFlow → Option DiagonalSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: restW =>
      match restW with
      | [] => none
      | W :: restB =>
          match restB with
          | [] => none
          | B :: restF =>
              match restF with
              | [] => none
              | F :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restR =>
                      match restR with
                      | [] => none
                      | R :: restH =>
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
                                                (DiagonalSequenceUp.mk
                                                  (diagonalSequenceDecodeBHist E)
                                                  (diagonalSequenceDecodeBHist W)
                                                  (diagonalSequenceDecodeBHist B)
                                                  (diagonalSequenceDecodeBHist F)
                                                  (diagonalSequenceDecodeBHist Q)
                                                  (diagonalSequenceDecodeBHist R)
                                                  (diagonalSequenceDecodeBHist H)
                                                  (diagonalSequenceDecodeBHist C)
                                                  (diagonalSequenceDecodeBHist P)
                                                  (diagonalSequenceDecodeBHist N))
                                          | _ :: _ => none

private theorem DiagonalSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiagonalSequenceUp,
      diagonalSequenceFromEventFlow (diagonalSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk E W B F Q R H C P N =>
      change
        some
          (DiagonalSequenceUp.mk
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist E))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist W))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist B))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist F))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist Q))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist R))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist H))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist C))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist P))
            (diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist N))) =
          some (DiagonalSequenceUp.mk E W B F Q R H C P N)
      rw [DiagonalSequenceTasteGate_single_carrier_alignment_decode E,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode W,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode B,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode F,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode Q,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode R,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode H,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode C,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode P,
        DiagonalSequenceTasteGate_single_carrier_alignment_decode N]

private theorem DiagonalSequenceToEventFlow_injective {x y : DiagonalSequenceUp} :
    diagonalSequenceToEventFlow x = diagonalSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalSequenceFromEventFlow (diagonalSequenceToEventFlow x) =
        diagonalSequenceFromEventFlow (diagonalSequenceToEventFlow y) :=
    congrArg diagonalSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiagonalSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiagonalSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance diagonalSequenceBHistCarrier : BHistCarrier DiagonalSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalSequenceToEventFlow
  fromEventFlow := diagonalSequenceFromEventFlow

instance diagonalSequenceChapterTasteGate : ChapterTasteGate DiagonalSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalSequenceFromEventFlow (diagonalSequenceToEventFlow x) = some x
    exact DiagonalSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiagonalSequenceToEventFlow_injective heq)

theorem DiagonalSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalSequenceDecodeBHist (diagonalSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DiagonalSequenceUp) ∧
        Nonempty (ChapterTasteGate DiagonalSequenceUp) ∧
          diagonalSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DiagonalSequenceTasteGate_single_carrier_alignment_decode,
      ⟨diagonalSequenceBHistCarrier⟩,
      ⟨diagonalSequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.DiagonalSequenceUp
