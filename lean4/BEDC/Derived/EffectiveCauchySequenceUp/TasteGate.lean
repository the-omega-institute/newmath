import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchySequenceUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchySequenceUp : Type where
  | mk (S M W D Q E H C P N : BHist) : EffectiveCauchySequenceUp
  deriving DecidableEq

def effectiveCauchySequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchySequenceEncodeBHist h

def effectiveCauchySequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchySequenceDecodeBHist tail)

private theorem effectiveCauchySequence_decode_encode_bhist :
    forall h : BHist,
      effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchySequenceFields : EffectiveCauchySequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchySequenceUp.mk S M W D Q E H C P N => [S, M, W, D, Q, E, H, C, P, N]

def effectiveCauchySequenceToEventFlow : EffectiveCauchySequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (effectiveCauchySequenceFields x).map effectiveCauchySequenceEncodeBHist

def effectiveCauchySequenceFromEventFlow : EventFlow -> Option EffectiveCauchySequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | M :: restM =>
          match restM with
          | W :: restW =>
              match restW with
              | D :: restD =>
                  match restD with
                  | Q :: restQ =>
                      match restQ with
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
                                                (EffectiveCauchySequenceUp.mk
                                                  (effectiveCauchySequenceDecodeBHist S)
                                                  (effectiveCauchySequenceDecodeBHist M)
                                                  (effectiveCauchySequenceDecodeBHist W)
                                                  (effectiveCauchySequenceDecodeBHist D)
                                                  (effectiveCauchySequenceDecodeBHist Q)
                                                  (effectiveCauchySequenceDecodeBHist E)
                                                  (effectiveCauchySequenceDecodeBHist H)
                                                  (effectiveCauchySequenceDecodeBHist C)
                                                  (effectiveCauchySequenceDecodeBHist P)
                                                  (effectiveCauchySequenceDecodeBHist N))
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

private theorem effectiveCauchySequence_mk_congr
    {S S' M M' W W' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hW : W' = W) (hD : D' = D)
    (hQ : Q' = Q) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    EffectiveCauchySequenceUp.mk S' M' W' D' Q' E' H' C' P' N' =
      EffectiveCauchySequenceUp.mk S M W D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hW
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem effectiveCauchySequence_round_trip :
    forall x : EffectiveCauchySequenceUp,
      effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W D Q E H C P N =>
      exact
        congrArg some
          (effectiveCauchySequence_mk_congr
            (effectiveCauchySequence_decode_encode_bhist S)
            (effectiveCauchySequence_decode_encode_bhist M)
            (effectiveCauchySequence_decode_encode_bhist W)
            (effectiveCauchySequence_decode_encode_bhist D)
            (effectiveCauchySequence_decode_encode_bhist Q)
            (effectiveCauchySequence_decode_encode_bhist E)
            (effectiveCauchySequence_decode_encode_bhist H)
            (effectiveCauchySequence_decode_encode_bhist C)
            (effectiveCauchySequence_decode_encode_bhist P)
            (effectiveCauchySequence_decode_encode_bhist N))

private theorem effectiveCauchySequenceToEventFlow_injective
    {x y : EffectiveCauchySequenceUp} :
    effectiveCauchySequenceToEventFlow x = effectiveCauchySequenceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) =
        effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow y) :=
    congrArg effectiveCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveCauchySequence_round_trip x).symm
      (Eq.trans hread (effectiveCauchySequence_round_trip y)))

private theorem effectiveCauchySequence_field_faithful :
    forall x y : EffectiveCauchySequenceUp,
      effectiveCauchySequenceFields x = effectiveCauchySequenceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S M W D Q E H C P N =>
      cases y with
      | mk S' M' W' D' Q' E' H' C' P' N' =>
          cases hfields
          rfl

instance effectiveCauchySequenceBHistCarrier :
    BHistCarrier EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchySequenceToEventFlow
  fromEventFlow := effectiveCauchySequenceFromEventFlow

instance effectiveCauchySequenceChapterTasteGate :
    ChapterTasteGate EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) =
      some x
    exact effectiveCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveCauchySequenceToEventFlow_injective heq)

instance effectiveCauchySequenceFieldFaithful :
    FieldFaithful EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveCauchySequenceFields
  field_faithful := effectiveCauchySequence_field_faithful

instance effectiveCauchySequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EffectiveCauchySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EffectiveCauchySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EffectiveCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCauchySequenceChapterTasteGate

theorem EffectiveCauchySequenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
        effectiveCauchySequenceDecodeBHist
          (effectiveCauchySequenceEncodeBHist h) = h) /\
      (forall x : EffectiveCauchySequenceUp,
        effectiveCauchySequenceFromEventFlow
          (effectiveCauchySequenceToEventFlow x) = some x) /\
      (forall x y : EffectiveCauchySequenceUp,
        effectiveCauchySequenceToEventFlow x =
          effectiveCauchySequenceToEventFlow y -> x = y) /\
      effectiveCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact effectiveCauchySequence_decode_encode_bhist
  constructor
  · exact effectiveCauchySequence_round_trip
  constructor
  · intro x y heq
    exact effectiveCauchySequenceToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.EffectiveCauchySequenceUp
