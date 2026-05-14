import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertificateAuditGateUp.TasteGate

open BEDC.FKernel.Hist
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
      [certificateAuditGateEncodeBHist gateInput,
        certificateAuditGateEncodeBHist checkedSurface,
        certificateAuditGateEncodeBHist refusal,
        certificateAuditGateEncodeBHist drift,
        certificateAuditGateEncodeBHist axiomPurity,
        certificateAuditGateEncodeBHist transport,
        certificateAuditGateEncodeBHist continuation,
        certificateAuditGateEncodeBHist provenance,
        certificateAuditGateEncodeBHist name]

def certificateAuditGateFromEventFlow : EventFlow -> Option CertificateAuditGateUp
  | [] => none
  | gateInput :: rest1 =>
      match rest1 with
      | [] => none
      | checkedSurface :: rest2 =>
          match rest2 with
          | [] => none
          | refusal :: rest3 =>
              match rest3 with
              | [] => none
              | drift :: rest4 =>
                  match rest4 with
                  | [] => none
                  | axiomPurity :: rest5 =>
                      match rest5 with
                      | [] => none
                      | transport :: rest6 =>
                          match rest6 with
                          | [] => none
                          | continuation :: rest7 =>
                              match rest7 with
                              | [] => none
                              | provenance :: rest8 =>
                                  match rest8 with
                                  | [] => none
                                  | name :: rest9 =>
                                      match rest9 with
                                      | [] =>
                                          some
                                            (CertificateAuditGateUp.mk
                                              (certificateAuditGateDecodeBHist gateInput)
                                              (certificateAuditGateDecodeBHist checkedSurface)
                                              (certificateAuditGateDecodeBHist refusal)
                                              (certificateAuditGateDecodeBHist drift)
                                              (certificateAuditGateDecodeBHist axiomPurity)
                                              (certificateAuditGateDecodeBHist transport)
                                              (certificateAuditGateDecodeBHist continuation)
                                              (certificateAuditGateDecodeBHist provenance)
                                              (certificateAuditGateDecodeBHist name))
                                      | _ :: _ => none

private theorem certificateAuditGate_round_trip :
    forall x : CertificateAuditGateUp,
      certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) = some x := by
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
  intro heq
  have hread :
      certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) =
        certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow y) :=
    congrArg certificateAuditGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (certificateAuditGate_round_trip x).symm
      (Eq.trans hread (certificateAuditGate_round_trip y)))

instance certificateAuditGateBHistCarrier : BHistCarrier CertificateAuditGateUp where
  toEventFlow := certificateAuditGateToEventFlow
  fromEventFlow := certificateAuditGateFromEventFlow

instance certificateAuditGateChapterTasteGate :
    ChapterTasteGate CertificateAuditGateUp where
  round_trip := by
    intro x
    exact certificateAuditGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (certificateAuditGateToEventFlow_injective heq)

instance certificateAuditGateFieldFaithful :
    FieldFaithful CertificateAuditGateUp where
  fields := fun x =>
    match x with
    | CertificateAuditGateUp.mk gateInput checkedSurface refusal drift axiomPurity transport
        continuation provenance name =>
        [gateInput, checkedSurface, refusal, drift, axiomPurity, transport, continuation,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk gateInput1 checkedSurface1 refusal1 drift1 axiomPurity1 transport1 continuation1
        provenance1 name1 =>
        cases y with
        | mk gateInput2 checkedSurface2 refusal2 drift2 axiomPurity2 transport2 continuation2
            provenance2 name2 =>
            cases h
            rfl

instance certificateAuditGateNontrivial : Nontrivial CertificateAuditGateUp where
  witness_pair :=
    ⟨CertificateAuditGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CertificateAuditGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CertificateAuditGateUp :=
  certificateAuditGateChapterTasteGate

theorem CertificateAuditGateTasteGate_single_carrier_alignment :
    (forall h : BHist,
      certificateAuditGateDecodeBHist (certificateAuditGateEncodeBHist h) = h) /\
      (forall x : CertificateAuditGateUp,
        certificateAuditGateFromEventFlow (certificateAuditGateToEventFlow x) = some x) /\
        (forall x y : CertificateAuditGateUp,
          certificateAuditGateToEventFlow x = certificateAuditGateToEventFlow y -> x = y) /\
          Nonempty (ChapterTasteGate CertificateAuditGateUp) /\
            Nonempty (FieldFaithful CertificateAuditGateUp) /\
              Nonempty (Nontrivial CertificateAuditGateUp) := by
  constructor
  · exact certificateAuditGateDecode_encode_bhist
  · constructor
    · exact certificateAuditGate_round_trip
    · constructor
      · intro x y heq
        exact certificateAuditGateToEventFlow_injective heq
      · exact
          ⟨⟨certificateAuditGateChapterTasteGate⟩,
            ⟨certificateAuditGateFieldFaithful⟩,
            ⟨certificateAuditGateNontrivial⟩⟩

end BEDC.Derived.CertificateAuditGateUp.TasteGate

namespace BEDC.Derived.CertificateAuditGateUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CertificateAuditGateUp :=
  TasteGate.taste_gate

end BEDC.Derived.CertificateAuditGateUp
