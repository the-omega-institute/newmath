import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertificateAuditGateUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertificateAuditGateUp : Type where
  | mk
      (gateInput checkedSurface refusal drift axiomPurity transport continuation provenance
        name : BHist) :
      CertificateAuditGateUp
  deriving DecidableEq

def certificateAuditGateEncodeBHist : BHist -> RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: certificateAuditGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: certificateAuditGateEncodeBHist h

def certificateAuditGateDecodeBHist : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (certificateAuditGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (certificateAuditGateDecodeBHist tail)

private theorem certificateAuditGateDecode_encode_bhist :
    forall h : BHist,
      certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def certificateAuditGateToEventFlow : CertificateAuditGateUp -> EventFlow
  | CertificateAuditGateUp.mk gateInput checkedSurface refusal drift axiomPurity transport
      continuation provenance name =>
      [[BMark.b0],
        certificateAuditGateEncodeBHist gateInput,
        [BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist checkedSurface,
        [BMark.b1, BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist drift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist axiomPurity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        certificateAuditGateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        certificateAuditGateEncodeBHist name]

def certificateAuditGateFromEventFlow : EventFlow -> Option CertificateAuditGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gateInput :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | checkedSurface :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | drift :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          none
                                      | axiomPurity :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CertificateAuditGateUp.mk
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    gateInput)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    checkedSurface)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    refusal)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    drift)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    axiomPurity)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    transport)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    continuation)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    provenance)
                                                                                  (certificateAuditGateDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem certificateAuditGate_round_trip :
    forall x : CertificateAuditGateUp,
      certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gateInput checkedSurface refusal drift axiomPurity transport continuation provenance
      name =>
      change
        some
          (CertificateAuditGateUp.mk
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist gateInput))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist checkedSurface))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist refusal))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist drift))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist axiomPurity))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist transport))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist continuation))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist provenance))
            (certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist name))) =
          some
            (CertificateAuditGateUp.mk gateInput checkedSurface refusal drift axiomPurity
              transport continuation provenance name)
      rw [certificateAuditGateDecode_encode_bhist gateInput,
        certificateAuditGateDecode_encode_bhist checkedSurface,
        certificateAuditGateDecode_encode_bhist refusal,
        certificateAuditGateDecode_encode_bhist drift,
        certificateAuditGateDecode_encode_bhist axiomPurity,
        certificateAuditGateDecode_encode_bhist transport,
        certificateAuditGateDecode_encode_bhist continuation,
        certificateAuditGateDecode_encode_bhist provenance,
        certificateAuditGateDecode_encode_bhist name]

private theorem certificateAuditGateToEventFlow_injective
    {x y : CertificateAuditGateUp} :
    certificateAuditGateToEventFlow x = certificateAuditGateToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) =
        certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow y) :=
    congrArg certificateAuditGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (certificateAuditGate_round_trip x).symm
      (Eq.trans hread (certificateAuditGate_round_trip y)))

instance certificateAuditGateBHistCarrier : BHistCarrier CertificateAuditGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := certificateAuditGateToEventFlow
  fromEventFlow := certificateAuditGateFromEventFlow

private def certificateAuditGateChapterTasteGateConcrete :
    @ChapterTasteGate CertificateAuditGateUp certificateAuditGateBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) = some x
    exact certificateAuditGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (certificateAuditGateToEventFlow_injective heq)

instance certificateAuditGateChapterTasteGate :
    ChapterTasteGate CertificateAuditGateUp :=
  certificateAuditGateChapterTasteGateConcrete

def certificateAuditGateFields : CertificateAuditGateUp -> List BHist
  | CertificateAuditGateUp.mk gateInput checkedSurface refusal drift axiomPurity transport
      continuation provenance name =>
      [gateInput, checkedSurface, refusal, drift, axiomPurity, transport, continuation,
        provenance, name]

private theorem certificateAuditGate_field_faithful :
    forall x y : CertificateAuditGateUp,
      certificateAuditGateFields x = certificateAuditGateFields y -> x = y := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk gateInput1 checkedSurface1 refusal1 drift1 axiomPurity1 transport1 continuation1
        provenance1 name1 =>
        cases y with
        | mk gateInput2 checkedSurface2 refusal2 drift2 axiomPurity2 transport2 continuation2
            provenance2 name2 =>
            cases h
            rfl

private def certificateAuditGateFieldFaithfulConcrete :
    @FieldFaithful CertificateAuditGateUp certificateAuditGateBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  fields := certificateAuditGateFields
  field_faithful := certificateAuditGate_field_faithful

instance certificateAuditGateFieldFaithful :
    FieldFaithful CertificateAuditGateUp :=
  certificateAuditGateFieldFaithfulConcrete

private def certificateAuditGateWitnessPair :
    Σ' (x : CertificateAuditGateUp) (y : CertificateAuditGateUp), x ≠ y :=
  ⟨CertificateAuditGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    CertificateAuditGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      intro h
      cases h⟩

private def certificateAuditGateNontrivialConcrete : Nontrivial CertificateAuditGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := certificateAuditGateWitnessPair

instance certificateAuditGateNontrivial : Nontrivial CertificateAuditGateUp :=
  certificateAuditGateNontrivialConcrete

def taste_gate : ChapterTasteGate CertificateAuditGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  certificateAuditGateChapterTasteGateConcrete

theorem CertificateAuditGateTasteGate_single_carrier_alignment :
    (forall h : BHist,
      certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist h) = h) /\
      (forall x : CertificateAuditGateUp,
        certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) = some x) /\
        (forall x y : CertificateAuditGateUp,
          certificateAuditGateToEventFlow x = certificateAuditGateToEventFlow y -> x = y) /\
          (forall x y : CertificateAuditGateUp,
            x ≠ y -> certificateAuditGateToEventFlow x ≠ certificateAuditGateToEventFlow y) /\
            (forall x y : CertificateAuditGateUp,
              certificateAuditGateFields x = certificateAuditGateFields y -> x = y) /\
              Nonempty (Σ' (x : CertificateAuditGateUp) (y : CertificateAuditGateUp), x ≠ y) /\
                certificateAuditGateEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact certificateAuditGateDecode_encode_bhist
  · constructor
    · exact certificateAuditGate_round_trip
    · constructor
      · intro x y heq
        exact certificateAuditGateToEventFlow_injective heq
      · constructor
        · intro x y hxy heq
          exact hxy (certificateAuditGateToEventFlow_injective heq)
        · constructor
          · exact certificateAuditGate_field_faithful
          · constructor
            · exact ⟨certificateAuditGateWitnessPair⟩
            · rfl

theorem CertificateAuditGateSoundnessBoundary
    (gateInput checkedSurface refusal drift axiomPurity transport continuation provenance
      name : BHist) :
    certificateAuditGateFields
        (CertificateAuditGateUp.mk gateInput checkedSurface refusal drift axiomPurity
          transport continuation provenance name) =
          [gateInput, checkedSurface, refusal, drift, axiomPurity, transport, continuation,
            provenance, name] /\
      Cont (append checkedSurface drift) axiomPurity
        (append (append checkedSurface drift) axiomPurity) /\
        hsame (append (append checkedSurface drift) axiomPurity)
          (append (append checkedSurface drift) axiomPurity) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

end BEDC.Derived.CertificateAuditGateUp.TasteGate

namespace BEDC.Derived.CertificateAuditGateUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CertificateAuditGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CertificateAuditGateUp
