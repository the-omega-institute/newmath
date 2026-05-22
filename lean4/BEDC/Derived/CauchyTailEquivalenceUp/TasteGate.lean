import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEquivalenceUp : Type where
  | mk :
      (sourceLeft sourceRight window threshold dyadic tail transport replay provenance
        localName : BHist) ->
        CauchyTailEquivalenceUp
  deriving DecidableEq

def cauchyTailEquivalenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailEquivalenceEncodeBHist h

def cauchyTailEquivalenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailEquivalenceDecodeBHist tail)

theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailEquivalenceFields : CauchyTailEquivalenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEquivalenceUp.mk sourceLeft sourceRight window threshold dyadic tail
      transport replay provenance localName =>
      [sourceLeft, sourceRight, window, threshold, dyadic, tail, transport, replay,
        provenance, localName]

def cauchyTailEquivalenceToEventFlow : CauchyTailEquivalenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailEquivalenceFields x).map cauchyTailEquivalenceEncodeBHist

def cauchyTailEquivalenceFromEventFlow : EventFlow -> Option CauchyTailEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceLeft :: rest0 =>
      match rest0 with
      | [] => none
      | sourceRight :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | threshold :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadic :: rest4 =>
                      match rest4 with
                      | [] => none
                      | tail :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyTailEquivalenceUp.mk
                                                  (cauchyTailEquivalenceDecodeBHist sourceLeft)
                                                  (cauchyTailEquivalenceDecodeBHist sourceRight)
                                                  (cauchyTailEquivalenceDecodeBHist window)
                                                  (cauchyTailEquivalenceDecodeBHist threshold)
                                                  (cauchyTailEquivalenceDecodeBHist dyadic)
                                                  (cauchyTailEquivalenceDecodeBHist tail)
                                                  (cauchyTailEquivalenceDecodeBHist transport)
                                                  (cauchyTailEquivalenceDecodeBHist replay)
                                                  (cauchyTailEquivalenceDecodeBHist provenance)
                                                  (cauchyTailEquivalenceDecodeBHist localName))
                                          | _ :: _ => none

theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyTailEquivalenceUp,
      cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight window threshold dyadic tail transport replay provenance
      localName =>
      change
        some
          (CauchyTailEquivalenceUp.mk
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist sourceLeft))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist sourceRight))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist window))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist threshold))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist dyadic))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist tail))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist transport))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist replay))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist provenance))
            (cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist localName))) =
          some
            (CauchyTailEquivalenceUp.mk sourceLeft sourceRight window threshold dyadic tail
              transport replay provenance localName)
      rw [CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode sourceLeft,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode sourceRight,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode window,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode threshold,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode dyadic,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode tail,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode localName]

theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailEquivalenceUp} :
    cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) =
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow y) :=
    congrArg cauchyTailEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyTailEquivalenceBHistCarrier : BHistCarrier CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailEquivalenceToEventFlow
  fromEventFlow := cauchyTailEquivalenceFromEventFlow

instance cauchyTailEquivalenceChapterTasteGate : ChapterTasteGate CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyTailEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailEquivalenceChapterTasteGate

theorem CauchyTailEquivalenceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchyTailEquivalenceUp,
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailEquivalenceUp,
          cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y -> x = y) ∧
          cauchyTailEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyTailEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

namespace TasteGate

theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchyTailEquivalenceUp,
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailEquivalenceUp,
          cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y -> x = y) ∧
          cauchyTailEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact CauchyTailEquivalenceUpTasteGate_single_carrier_alignment

def taste_gate : ChapterTasteGate CauchyTailEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.CauchyTailEquivalenceUp.taste_gate

end TasteGate

end BEDC.Derived.CauchyTailEquivalenceUp
