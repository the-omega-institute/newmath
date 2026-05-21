import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyControlSequenceUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyControlSequenceUp : Type where
  | mk (R W D M E H C P N : BHist) : CauchyControlSequenceUp
  deriving DecidableEq

def cauchyControlSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyControlSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyControlSequenceEncodeBHist h

def cauchyControlSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyControlSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyControlSequenceDecodeBHist tail)

private theorem CauchyControlSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyControlSequenceDecodeBHist (cauchyControlSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyControlSequenceFields : CauchyControlSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyControlSequenceUp.mk R W D M E H C P N => [R, W, D, M, E, H, C, P, N]

def cauchyControlSequenceToEventFlow : CauchyControlSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyControlSequenceFields x).map cauchyControlSequenceEncodeBHist

def cauchyControlSequenceFromEventFlow : EventFlow → Option CauchyControlSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: restR =>
      match restR with
      | W :: restW =>
          match restW with
          | D :: restD =>
              match restD with
              | M :: restM =>
                  match restM with
                  | E :: restE =>
                      match restE with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (CauchyControlSequenceUp.mk
                                              (cauchyControlSequenceDecodeBHist R)
                                              (cauchyControlSequenceDecodeBHist W)
                                              (cauchyControlSequenceDecodeBHist D)
                                              (cauchyControlSequenceDecodeBHist M)
                                              (cauchyControlSequenceDecodeBHist E)
                                              (cauchyControlSequenceDecodeBHist H)
                                              (cauchyControlSequenceDecodeBHist C)
                                              (cauchyControlSequenceDecodeBHist P)
                                              (cauchyControlSequenceDecodeBHist N))
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

private theorem cauchyControlSequence_mk_congr
    {R R' W W' D D' M M' E E' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hW : W' = W) (hD : D' = D) (hM : M' = M)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    CauchyControlSequenceUp.mk R' W' D' M' E' H' C' P' N' =
      CauchyControlSequenceUp.mk R W D M E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hW
  cases hD
  cases hM
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyControlSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyControlSequenceUp,
      cauchyControlSequenceFromEventFlow (cauchyControlSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D M E H C P N =>
      exact
        congrArg some
          (cauchyControlSequence_mk_congr
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode R)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode W)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode D)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode M)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode E)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode H)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode C)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode P)
            (CauchyControlSequenceTasteGate_single_carrier_alignment_decode N))

private theorem cauchyControlSequenceToEventFlow_injective
    {x y : CauchyControlSequenceUp} :
    cauchyControlSequenceToEventFlow x = cauchyControlSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyControlSequenceFromEventFlow (cauchyControlSequenceToEventFlow x) =
        cauchyControlSequenceFromEventFlow (cauchyControlSequenceToEventFlow y) :=
    congrArg cauchyControlSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyControlSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyControlSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyControlSequence_field_faithful :
    ∀ x y : CauchyControlSequenceUp,
      cauchyControlSequenceFields x = cauchyControlSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R W D M E H C P N =>
      cases y with
      | mk R' W' D' M' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyControlSequenceBHistCarrier : BHistCarrier CauchyControlSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyControlSequenceToEventFlow
  fromEventFlow := cauchyControlSequenceFromEventFlow

instance cauchyControlSequenceChapterTasteGate :
    ChapterTasteGate CauchyControlSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyControlSequenceFromEventFlow (cauchyControlSequenceToEventFlow x) = some x
    exact CauchyControlSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyControlSequenceToEventFlow_injective heq)

instance cauchyControlSequenceFieldFaithful : FieldFaithful CauchyControlSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyControlSequenceFields
  field_faithful := cauchyControlSequence_field_faithful

instance cauchyControlSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyControlSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyControlSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyControlSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyControlSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyControlSequenceChapterTasteGate

theorem CauchyControlSequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyControlSequenceUp) ∧
      Nonempty (FieldFaithful CauchyControlSequenceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyControlSequenceUp) ∧
      (∀ h : BHist,
        cauchyControlSequenceDecodeBHist (cauchyControlSequenceEncodeBHist h) = h) ∧
      (∀ x : CauchyControlSequenceUp,
        cauchyControlSequenceFromEventFlow (cauchyControlSequenceToEventFlow x) = some x) ∧
      (∀ x y : CauchyControlSequenceUp,
        cauchyControlSequenceToEventFlow x = cauchyControlSequenceToEventFlow y → x = y) ∧
      cauchyControlSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyControlSequenceChapterTasteGate⟩
  constructor
  · exact ⟨cauchyControlSequenceFieldFaithful⟩
  constructor
  · exact ⟨cauchyControlSequenceNontrivial⟩
  constructor
  · exact CauchyControlSequenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyControlSequenceTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyControlSequenceToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CauchyControlSequenceUp
