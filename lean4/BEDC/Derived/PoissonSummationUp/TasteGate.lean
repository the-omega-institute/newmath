import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoissonSummationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoissonSummationUp : Type where
  | mk :
      (latticeRow fourierRow distributionRow summationWindow realReadback transportRow
        replayRow provenanceRow localName : BHist) ->
        PoissonSummationUp
  deriving DecidableEq

def poissonSummationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poissonSummationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poissonSummationEncodeBHist h

def poissonSummationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poissonSummationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poissonSummationDecodeBHist tail)

theorem PoissonSummationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, poissonSummationDecodeBHist (poissonSummationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def poissonSummationFields : PoissonSummationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoissonSummationUp.mk latticeRow fourierRow distributionRow summationWindow
      realReadback transportRow replayRow provenanceRow localName =>
      [latticeRow, fourierRow, distributionRow, summationWindow, realReadback,
        transportRow, replayRow, provenanceRow, localName]

def poissonSummationToEventFlow : PoissonSummationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poissonSummationFields x).map poissonSummationEncodeBHist

def poissonSummationFromEventFlow : EventFlow -> Option PoissonSummationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | latticeRow :: rest0 =>
      match rest0 with
      | [] => none
      | fourierRow :: rest1 =>
          match rest1 with
          | [] => none
          | distributionRow :: rest2 =>
              match rest2 with
              | [] => none
              | summationWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transportRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replayRow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenanceRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (PoissonSummationUp.mk
                                              (poissonSummationDecodeBHist latticeRow)
                                              (poissonSummationDecodeBHist fourierRow)
                                              (poissonSummationDecodeBHist distributionRow)
                                              (poissonSummationDecodeBHist summationWindow)
                                              (poissonSummationDecodeBHist realReadback)
                                              (poissonSummationDecodeBHist transportRow)
                                              (poissonSummationDecodeBHist replayRow)
                                              (poissonSummationDecodeBHist provenanceRow)
                                              (poissonSummationDecodeBHist localName))
                                      | _ :: _ => none

theorem PoissonSummationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PoissonSummationUp,
      poissonSummationFromEventFlow (poissonSummationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk latticeRow fourierRow distributionRow summationWindow realReadback transportRow
      replayRow provenanceRow localName =>
      change
        some
          (PoissonSummationUp.mk
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist latticeRow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist fourierRow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist distributionRow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist summationWindow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist realReadback))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist transportRow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist replayRow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist provenanceRow))
            (poissonSummationDecodeBHist (poissonSummationEncodeBHist localName))) =
          some
            (PoissonSummationUp.mk latticeRow fourierRow distributionRow summationWindow
              realReadback transportRow replayRow provenanceRow localName)
      rw [PoissonSummationTasteGate_single_carrier_alignment_decode_encode latticeRow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode fourierRow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode distributionRow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode summationWindow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode realReadback,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode transportRow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode replayRow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode provenanceRow,
        PoissonSummationTasteGate_single_carrier_alignment_decode_encode localName]

private theorem PoissonSummationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PoissonSummationUp} :
    poissonSummationToEventFlow x = poissonSummationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poissonSummationFromEventFlow (poissonSummationToEventFlow x) =
        poissonSummationFromEventFlow (poissonSummationToEventFlow y) :=
    congrArg poissonSummationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PoissonSummationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PoissonSummationTasteGate_single_carrier_alignment_round_trip y)))

instance poissonSummationBHistCarrier : BHistCarrier PoissonSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poissonSummationToEventFlow
  fromEventFlow := poissonSummationFromEventFlow

instance poissonSummationChapterTasteGate : ChapterTasteGate PoissonSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (PoissonSummationTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (PoissonSummationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PoissonSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  poissonSummationChapterTasteGate

theorem PoissonSummationTasteGate_single_carrier_alignment :
    (∀ h : BHist, poissonSummationDecodeBHist (poissonSummationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PoissonSummationUp) ∧
        Nonempty (ChapterTasteGate PoissonSummationUp) ∧
          poissonSummationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PoissonSummationTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨poissonSummationBHistCarrier⟩
    · constructor
      · exact ⟨poissonSummationChapterTasteGate⟩
      · rfl

end BEDC.Derived.PoissonSummationUp
