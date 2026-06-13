import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDoubleSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDoubleSequenceUp : Type where
  | mk (X mu tau D R E H C P N : BHist) : CauchyDoubleSequenceUp
  deriving DecidableEq

def cauchyDoubleSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDoubleSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDoubleSequenceEncodeBHist h

def cauchyDoubleSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDoubleSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDoubleSequenceDecodeBHist tail)

private theorem CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyDoubleSequenceFields : CauchyDoubleSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDoubleSequenceUp.mk X mu tau D R E H C P N => [X, mu, tau, D, R, E, H, C, P, N]

def cauchyDoubleSequenceToEventFlow : CauchyDoubleSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyDoubleSequenceFields x).map cauchyDoubleSequenceEncodeBHist

def cauchyDoubleSequenceFromEventFlow : EventFlow → Option CauchyDoubleSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | mu :: restMu =>
          match restMu with
          | tau :: restTau =>
              match restTau with
              | D :: restD =>
                  match restD with
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
                                                (CauchyDoubleSequenceUp.mk
                                                  (cauchyDoubleSequenceDecodeBHist X)
                                                  (cauchyDoubleSequenceDecodeBHist mu)
                                                  (cauchyDoubleSequenceDecodeBHist tau)
                                                  (cauchyDoubleSequenceDecodeBHist D)
                                                  (cauchyDoubleSequenceDecodeBHist R)
                                                  (cauchyDoubleSequenceDecodeBHist E)
                                                  (cauchyDoubleSequenceDecodeBHist H)
                                                  (cauchyDoubleSequenceDecodeBHist C)
                                                  (cauchyDoubleSequenceDecodeBHist P)
                                                  (cauchyDoubleSequenceDecodeBHist N))
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

private theorem CauchyDoubleSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyDoubleSequenceUp,
      cauchyDoubleSequenceFromEventFlow (cauchyDoubleSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X mu tau D R E H C P N =>
      change
        some
          (CauchyDoubleSequenceUp.mk
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist X))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist mu))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist tau))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist D))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist R))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist E))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist H))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist C))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist P))
            (cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist N))) =
          some (CauchyDoubleSequenceUp.mk X mu tau D R E H C P N)
      rw [CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode X,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode mu,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode tau,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode D,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode R,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode E,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode H,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode C,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode P,
        CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode N]

private theorem cauchyDoubleSequenceToEventFlow_injective {x y : CauchyDoubleSequenceUp} :
    cauchyDoubleSequenceToEventFlow x = cauchyDoubleSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDoubleSequenceFromEventFlow (cauchyDoubleSequenceToEventFlow x) =
        cauchyDoubleSequenceFromEventFlow (cauchyDoubleSequenceToEventFlow y) :=
    congrArg cauchyDoubleSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyDoubleSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyDoubleSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyDoubleSequence_field_faithful :
    ∀ x y : CauchyDoubleSequenceUp,
      cauchyDoubleSequenceFields x = cauchyDoubleSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 mu1 tau1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 mu2 tau2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyDoubleSequenceBHistCarrier : BHistCarrier CauchyDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDoubleSequenceToEventFlow
  fromEventFlow := cauchyDoubleSequenceFromEventFlow

instance cauchyDoubleSequenceChapterTasteGate :
    ChapterTasteGate CauchyDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDoubleSequenceFromEventFlow (cauchyDoubleSequenceToEventFlow x) = some x
    exact CauchyDoubleSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDoubleSequenceToEventFlow_injective heq)

instance cauchyDoubleSequenceFieldFaithful : FieldFaithful CauchyDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyDoubleSequenceFields
  field_faithful := cauchyDoubleSequence_field_faithful

instance cauchyDoubleSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyDoubleSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyDoubleSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyDoubleSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyDoubleSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDoubleSequenceChapterTasteGate

theorem CauchyDoubleSequenceTasteGate_single_carrier_alignment :
    cauchyDoubleSequenceEncodeBHist BHist.Empty = [] ∧
      (∀ h : BHist,
        cauchyDoubleSequenceDecodeBHist (cauchyDoubleSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyDoubleSequenceUp) ∧
      Nonempty (ChapterTasteGate CauchyDoubleSequenceUp) ∧
      Nonempty (FieldFaithful CauchyDoubleSequenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · rfl
  constructor
  · exact CauchyDoubleSequenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact ⟨cauchyDoubleSequenceBHistCarrier⟩
  constructor
  · exact ⟨cauchyDoubleSequenceChapterTasteGate⟩
  · exact ⟨cauchyDoubleSequenceFieldFaithful⟩

end BEDC.Derived.CauchyDoubleSequenceUp
