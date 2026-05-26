import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealizerSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealizerSequenceUp : Type where
  | mk (S W R D E H C P N : BHist) : CauchyRealizerSequenceUp
  deriving DecidableEq

def cauchyRealizerSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealizerSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealizerSequenceEncodeBHist h

def cauchyRealizerSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealizerSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealizerSequenceDecodeBHist tail)

private theorem CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealizerSequenceFields : CauchyRealizerSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealizerSequenceUp.mk S W R D E H C P N => [S, W, R, D, E, H, C, P, N]

def cauchyRealizerSequenceToEventFlow :
    CauchyRealizerSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealizerSequenceUp.mk S W R D E H C P N =>
      [cauchyRealizerSequenceEncodeBHist S,
        cauchyRealizerSequenceEncodeBHist W,
        cauchyRealizerSequenceEncodeBHist R,
        cauchyRealizerSequenceEncodeBHist D,
        cauchyRealizerSequenceEncodeBHist E,
        cauchyRealizerSequenceEncodeBHist H,
        cauchyRealizerSequenceEncodeBHist C,
        cauchyRealizerSequenceEncodeBHist P,
        cauchyRealizerSequenceEncodeBHist N]

def cauchyRealizerSequenceFromEventFlow : EventFlow → Option CauchyRealizerSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restW =>
      match restW with
      | [] => none
      | W :: restR =>
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
                                            (CauchyRealizerSequenceUp.mk
                                              (cauchyRealizerSequenceDecodeBHist S)
                                              (cauchyRealizerSequenceDecodeBHist W)
                                              (cauchyRealizerSequenceDecodeBHist R)
                                              (cauchyRealizerSequenceDecodeBHist D)
                                              (cauchyRealizerSequenceDecodeBHist E)
                                              (cauchyRealizerSequenceDecodeBHist H)
                                              (cauchyRealizerSequenceDecodeBHist C)
                                              (cauchyRealizerSequenceDecodeBHist P)
                                              (cauchyRealizerSequenceDecodeBHist N))
                                      | _ :: _ => none

private theorem CauchyRealizerSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealizerSequenceUp,
      cauchyRealizerSequenceFromEventFlow (cauchyRealizerSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S W R D E H C P N =>
      change
        some
          (CauchyRealizerSequenceUp.mk
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist S))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist W))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist R))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist D))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist E))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist H))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist C))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist P))
            (cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist N))) =
          some (CauchyRealizerSequenceUp.mk S W R D E H C P N)
      rw [CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode S,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode W,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode R,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode D,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode E,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode H,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode C,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode P,
        CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode N]

private theorem CauchyRealizerSequenceTasteGate_single_carrier_alignment_injective
    {x y : CauchyRealizerSequenceUp} :
    cauchyRealizerSequenceToEventFlow x = cauchyRealizerSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealizerSequenceFromEventFlow (cauchyRealizerSequenceToEventFlow x) =
        cauchyRealizerSequenceFromEventFlow (cauchyRealizerSequenceToEventFlow y) :=
    congrArg cauchyRealizerSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealizerSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealizerSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRealizerSequenceBHistCarrier : BHistCarrier CauchyRealizerSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealizerSequenceToEventFlow
  fromEventFlow := cauchyRealizerSequenceFromEventFlow

instance cauchyRealizerSequenceChapterTasteGate :
    ChapterTasteGate CauchyRealizerSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealizerSequenceFromEventFlow (cauchyRealizerSequenceToEventFlow x) =
      some x
    exact CauchyRealizerSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealizerSequenceTasteGate_single_carrier_alignment_injective heq)

theorem CauchyRealizerSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealizerSequenceDecodeBHist (cauchyRealizerSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyRealizerSequenceUp) ∧
        Nonempty (ChapterTasteGate CauchyRealizerSequenceUp) ∧
          cauchyRealizerSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyRealizerSequenceTasteGate_single_carrier_alignment_decode,
      ⟨cauchyRealizerSequenceBHistCarrier⟩, ⟨cauchyRealizerSequenceChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyRealizerSequenceUp
