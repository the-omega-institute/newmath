import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireGenericResidualUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireGenericResidualUp : Type where
  | mk :
      (bairePrefix denseSchedule metricHandoff streamSchedule windowLedger rationalReadback
        realSeal residualLedger transport replay provenance localName : BHist) →
        BaireGenericResidualUp
  deriving DecidableEq

def baireGenericResidualEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireGenericResidualEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireGenericResidualEncodeBHist h

def baireGenericResidualDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireGenericResidualDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireGenericResidualDecodeBHist tail)

theorem BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def baireGenericResidualFields : BaireGenericResidualUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireGenericResidualUp.mk bairePrefix denseSchedule metricHandoff streamSchedule
      windowLedger rationalReadback realSeal residualLedger transport replay provenance
      localName =>
      [bairePrefix, denseSchedule, metricHandoff, streamSchedule, windowLedger,
        rationalReadback, realSeal, residualLedger, transport, replay, provenance, localName]

def baireGenericResidualToEventFlow : BaireGenericResidualUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireGenericResidualFields x).map baireGenericResidualEncodeBHist

def baireGenericResidualFromEventFlow : EventFlow → Option BaireGenericResidualUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | bairePrefix :: rest0 =>
      match rest0 with
      | [] => none
      | denseSchedule :: rest1 =>
          match rest1 with
          | [] => none
          | metricHandoff :: rest2 =>
              match rest2 with
              | [] => none
              | streamSchedule :: rest3 =>
                  match rest3 with
                  | [] => none
                  | windowLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | rationalReadback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | residualLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (BaireGenericResidualUp.mk
                                                          (baireGenericResidualDecodeBHist
                                                            bairePrefix)
                                                          (baireGenericResidualDecodeBHist
                                                            denseSchedule)
                                                          (baireGenericResidualDecodeBHist
                                                            metricHandoff)
                                                          (baireGenericResidualDecodeBHist
                                                            streamSchedule)
                                                          (baireGenericResidualDecodeBHist
                                                            windowLedger)
                                                          (baireGenericResidualDecodeBHist
                                                            rationalReadback)
                                                          (baireGenericResidualDecodeBHist
                                                            realSeal)
                                                          (baireGenericResidualDecodeBHist
                                                            residualLedger)
                                                          (baireGenericResidualDecodeBHist
                                                            transport)
                                                          (baireGenericResidualDecodeBHist
                                                            replay)
                                                          (baireGenericResidualDecodeBHist
                                                            provenance)
                                                          (baireGenericResidualDecodeBHist
                                                            localName))
                                                  | _ :: _ => none

theorem BaireGenericResidualTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BaireGenericResidualUp,
      baireGenericResidualFromEventFlow (baireGenericResidualToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bairePrefix denseSchedule metricHandoff streamSchedule windowLedger rationalReadback
      realSeal residualLedger transport replay provenance localName =>
      change
        some
          (BaireGenericResidualUp.mk
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist bairePrefix))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist denseSchedule))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist metricHandoff))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist streamSchedule))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist windowLedger))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist rationalReadback))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist realSeal))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist residualLedger))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist transport))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist replay))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist provenance))
            (baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist localName))) =
          some
            (BaireGenericResidualUp.mk bairePrefix denseSchedule metricHandoff streamSchedule
              windowLedger rationalReadback realSeal residualLedger transport replay provenance
              localName)
      rw [BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode bairePrefix,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode denseSchedule,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode metricHandoff,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode streamSchedule,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode windowLedger,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode rationalReadback,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode realSeal,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode residualLedger,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode transport,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode replay,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode provenance,
        BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode localName]

theorem BaireGenericResidualTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireGenericResidualUp} :
    baireGenericResidualToEventFlow x = baireGenericResidualToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireGenericResidualFromEventFlow (baireGenericResidualToEventFlow x) =
        baireGenericResidualFromEventFlow (baireGenericResidualToEventFlow y) :=
    congrArg baireGenericResidualFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireGenericResidualTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireGenericResidualTasteGate_single_carrier_alignment_round_trip y)))

instance baireGenericResidualBHistCarrier : BHistCarrier BaireGenericResidualUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireGenericResidualToEventFlow
  fromEventFlow := baireGenericResidualFromEventFlow

instance baireGenericResidualChapterTasteGate : ChapterTasteGate BaireGenericResidualUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (BaireGenericResidualTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireGenericResidualTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BaireGenericResidualUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireGenericResidualChapterTasteGate

theorem BaireGenericResidualTasteGate_single_carrier_alignment :
    (∀ h : BHist, baireGenericResidualDecodeBHist (baireGenericResidualEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BaireGenericResidualUp) ∧
        Nonempty (ChapterTasteGate BaireGenericResidualUp) ∧
          baireGenericResidualEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BaireGenericResidualTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨baireGenericResidualBHistCarrier⟩
    · constructor
      · exact ⟨baireGenericResidualChapterTasteGate⟩
      · rfl

end BEDC.Derived.BaireGenericResidualUp
