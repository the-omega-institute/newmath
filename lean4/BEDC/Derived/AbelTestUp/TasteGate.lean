import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelTestUp : Type where
  | mk :
      (partialSums coefficient monotoneNull dyadicEstimate tailSchedule uniform regular
        realSeal transport continuation provenance localNameCert : BHist) ->
        AbelTestUp
  deriving DecidableEq

def abelTestEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelTestEncodeBHist h

def abelTestDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelTestDecodeBHist tail)

theorem AbelTestTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, abelTestDecodeBHist (abelTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def abelTestFields : AbelTestUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelTestUp.mk partialSums coefficient monotoneNull dyadicEstimate tailSchedule uniform
      regular realSeal transport continuation provenance localNameCert =>
      [partialSums, coefficient, monotoneNull, dyadicEstimate, tailSchedule, uniform, regular,
        realSeal, transport, continuation, provenance, localNameCert]

def abelTestToEventFlow : AbelTestUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (abelTestFields x).map abelTestEncodeBHist

def abelTestFromEventFlow : EventFlow -> Option AbelTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | partialSums :: rest0 =>
      match rest0 with
      | [] => none
      | coefficient :: rest1 =>
          match rest1 with
          | [] => none
          | monotoneNull :: rest2 =>
              match rest2 with
              | [] => none
              | dyadicEstimate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | tailSchedule :: rest4 =>
                      match rest4 with
                      | [] => none
                      | uniform :: rest5 =>
                          match rest5 with
                          | [] => none
                          | regular :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | continuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localNameCert :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (AbelTestUp.mk
                                                          (abelTestDecodeBHist partialSums)
                                                          (abelTestDecodeBHist coefficient)
                                                          (abelTestDecodeBHist monotoneNull)
                                                          (abelTestDecodeBHist dyadicEstimate)
                                                          (abelTestDecodeBHist tailSchedule)
                                                          (abelTestDecodeBHist uniform)
                                                          (abelTestDecodeBHist regular)
                                                          (abelTestDecodeBHist realSeal)
                                                          (abelTestDecodeBHist transport)
                                                          (abelTestDecodeBHist continuation)
                                                          (abelTestDecodeBHist provenance)
                                                          (abelTestDecodeBHist localNameCert))
                                                  | _ :: _ => none

theorem AbelTestTasteGate_single_carrier_alignment_round_trip :
    forall x : AbelTestUp, abelTestFromEventFlow (abelTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk partialSums coefficient monotoneNull dyadicEstimate tailSchedule uniform regular realSeal
      transport continuation provenance localNameCert =>
      change
        some
          (AbelTestUp.mk
            (abelTestDecodeBHist (abelTestEncodeBHist partialSums))
            (abelTestDecodeBHist (abelTestEncodeBHist coefficient))
            (abelTestDecodeBHist (abelTestEncodeBHist monotoneNull))
            (abelTestDecodeBHist (abelTestEncodeBHist dyadicEstimate))
            (abelTestDecodeBHist (abelTestEncodeBHist tailSchedule))
            (abelTestDecodeBHist (abelTestEncodeBHist uniform))
            (abelTestDecodeBHist (abelTestEncodeBHist regular))
            (abelTestDecodeBHist (abelTestEncodeBHist realSeal))
            (abelTestDecodeBHist (abelTestEncodeBHist transport))
            (abelTestDecodeBHist (abelTestEncodeBHist continuation))
            (abelTestDecodeBHist (abelTestEncodeBHist provenance))
            (abelTestDecodeBHist (abelTestEncodeBHist localNameCert))) =
          some
            (AbelTestUp.mk partialSums coefficient monotoneNull dyadicEstimate tailSchedule
              uniform regular realSeal transport continuation provenance localNameCert)
      rw [AbelTestTasteGate_single_carrier_alignment_decode_encode partialSums,
        AbelTestTasteGate_single_carrier_alignment_decode_encode coefficient,
        AbelTestTasteGate_single_carrier_alignment_decode_encode monotoneNull,
        AbelTestTasteGate_single_carrier_alignment_decode_encode dyadicEstimate,
        AbelTestTasteGate_single_carrier_alignment_decode_encode tailSchedule,
        AbelTestTasteGate_single_carrier_alignment_decode_encode uniform,
        AbelTestTasteGate_single_carrier_alignment_decode_encode regular,
        AbelTestTasteGate_single_carrier_alignment_decode_encode realSeal,
        AbelTestTasteGate_single_carrier_alignment_decode_encode transport,
        AbelTestTasteGate_single_carrier_alignment_decode_encode continuation,
        AbelTestTasteGate_single_carrier_alignment_decode_encode provenance,
        AbelTestTasteGate_single_carrier_alignment_decode_encode localNameCert]

theorem AbelTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelTestUp} :
    abelTestToEventFlow x = abelTestToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelTestFromEventFlow (abelTestToEventFlow x) =
        abelTestFromEventFlow (abelTestToEventFlow y) :=
    congrArg abelTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbelTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelTestTasteGate_single_carrier_alignment_round_trip y)))

theorem AbelTestTasteGate_single_carrier_alignment_field_faithful :
    forall x y : AbelTestUp, abelTestFields x = abelTestFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk partialSums₁ coefficient₁ monotoneNull₁ dyadicEstimate₁ tailSchedule₁ uniform₁ regular₁
      realSeal₁ transport₁ continuation₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk partialSums₂ coefficient₂ monotoneNull₂ dyadicEstimate₂ tailSchedule₂ uniform₂
          regular₂ realSeal₂ transport₂ continuation₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance abelTestBHistCarrier : BHistCarrier AbelTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelTestToEventFlow
  fromEventFlow := abelTestFromEventFlow

instance abelTestChapterTasteGate : ChapterTasteGate AbelTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (AbelTestTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance abelTestFieldFaithful : FieldFaithful AbelTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := abelTestFields
  field_faithful := AbelTestTasteGate_single_carrier_alignment_field_faithful

instance abelTestNontrivial : BEDC.Meta.TasteGate.Nontrivial AbelTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbelTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AbelTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def abelTestTasteGate : ChapterTasteGate AbelTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelTestChapterTasteGate

theorem AbelTestTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AbelTestUp) ∧
      Nonempty (FieldFaithful AbelTestUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AbelTestUp) ∧
          (∀ h : BHist, abelTestDecodeBHist (abelTestEncodeBHist h) = h) ∧
            (∀ x : AbelTestUp, abelTestFromEventFlow (abelTestToEventFlow x) = some x) ∧
              (∀ x y : AbelTestUp,
                abelTestToEventFlow x = abelTestToEventFlow y -> x = y) ∧
                abelTestEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨abelTestChapterTasteGate⟩
  · constructor
    · exact ⟨abelTestFieldFaithful⟩
    · constructor
      · exact ⟨abelTestNontrivial⟩
      · constructor
        · exact AbelTestTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact AbelTestTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact AbelTestTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.AbelTestUp
