import BEDC.Derived.FieldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.EllipticCurveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FieldUp

theorem EllipticCurveCarrierPacket_field_source_obligation [AskSetup] [PackageSetup]
    {fieldCoeff cubic discriminant : BHist} {tokenBundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    FieldSingletonCarrier fieldCoeff ->
      UnaryHistory cubic ->
        Cont fieldCoeff cubic discriminant ->
          TokIntro tokenBundle discriminant pkg ->
            UnaryHistory discriminant ∧ FieldSingletonCarrier fieldCoeff ∧
              hsame fieldCoeff BHist.Empty ∧ TokIntro tokenBundle discriminant pkg ∧
                Cont fieldCoeff cubic discriminant := by
  intro fieldCarrier cubicUnary discriminantCont token
  have fieldUnary : UnaryHistory fieldCoeff :=
    unary_transport unary_empty (hsame_symm fieldCarrier)
  have discriminantUnary : UnaryHistory discriminant :=
    unary_cont_closed fieldUnary cubicUnary discriminantCont
  exact And.intro discriminantUnary
      (And.intro fieldCarrier
        (And.intro fieldCarrier
          (And.intro token discriminantCont)))

def EllipticCurveCarrierPacket
    (field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist) : Prop :=
  UnaryHistory field ∧ UnaryHistory projective ∧ UnaryHistory coeffs ∧
    UnaryHistory basePoint ∧ Cont field projective fieldLedger ∧
      Cont coeffs cubic projectiveLedger ∧ Cont smooth basePoint provenance

theorem EllipticCurveCarrierPacket_field_projective_source_rows
    {field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      UnaryHistory field ∧ UnaryHistory projective ∧ UnaryHistory coeffs ∧
        UnaryHistory basePoint ∧ hsame fieldLedger (append field projective) ∧
          hsame projectiveLedger (append coeffs cubic) ∧
            hsame provenance (append smooth basePoint) := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
           (And.intro packet.right.right.right.right.left
             (And.intro packet.right.right.right.right.right.left
               packet.right.right.right.right.right.right)))))

theorem EllipticCurveCarrierPacket_basepoint_stability_obligation
    {field projective coeffs cubic smooth basePoint basePoint' fieldLedger projectiveLedger
      provenance provenance' : BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      hsame basePoint basePoint' ->
        Cont smooth basePoint' provenance' ->
          EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint' fieldLedger
              projectiveLedger provenance' ∧
            hsame provenance provenance' := by
  intro packet sameBasePoint provenanceCont
  have basePointUnary : UnaryHistory basePoint' :=
    unary_transport packet.right.right.right.left sameBasePoint
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl smooth) sameBasePoint
      packet.right.right.right.right.right.right provenanceCont
  constructor
  · exact And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro basePointUnary
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left provenanceCont)))))
  · exact sameProvenance

theorem EllipticCurveCarrierPacket_projective_genus_one_obligation
    {field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      UnaryHistory cubic ->
        UnaryHistory smooth ->
          UnaryHistory projective ∧ UnaryHistory projectiveLedger ∧
            UnaryHistory provenance ∧ Cont coeffs cubic projectiveLedger ∧
              Cont smooth basePoint provenance := by
  intro packet cubicUnary smoothUnary
  have projectiveLedgerUnary : UnaryHistory projectiveLedger :=
    unary_cont_closed packet.right.right.left cubicUnary
      packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed smoothUnary packet.right.right.right.left
      packet.right.right.right.right.right.right
  exact And.intro packet.right.left
    (And.intro projectiveLedgerUnary
      (And.intro provenanceUnary
        (And.intro packet.right.right.right.right.right.left
          packet.right.right.right.right.right.right)))

theorem EllipticCurveCarrierPacket_smooth_projective_carrier_obligation
    {field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      UnaryHistory cubic ->
        UnaryHistory smooth ->
          UnaryHistory field ∧ UnaryHistory projective ∧ UnaryHistory coeffs ∧
            UnaryHistory cubic ∧ UnaryHistory smooth ∧ UnaryHistory basePoint ∧
              Cont field projective fieldLedger ∧ Cont coeffs cubic projectiveLedger ∧
                Cont smooth basePoint provenance ∧ hsame fieldLedger (append field projective) ∧
                  hsame projectiveLedger (append coeffs cubic) ∧
                    hsame provenance (append smooth basePoint) := by
  intro packet cubicUnary smoothUnary
  have sourceRows :=
    EllipticCurveCarrierPacket_field_projective_source_rows packet
  have genusRows :=
    EllipticCurveCarrierPacket_projective_genus_one_obligation packet cubicUnary smoothUnary
  exact And.intro sourceRows.left
    (And.intro sourceRows.right.left
      (And.intro sourceRows.right.right.left
        (And.intro cubicUnary
          (And.intro smoothUnary
            (And.intro sourceRows.right.right.right.left
              (And.intro packet.right.right.right.right.left
                (And.intro genusRows.right.right.right.left
                  (And.intro genusRows.right.right.right.right
                    (And.intro sourceRows.right.right.right.right.left
                      (And.intro sourceRows.right.right.right.right.right.left
                        sourceRows.right.right.right.right.right.right))))))))))

theorem EllipticCurveCarrierPacket_classifier_transport_obligation
    {field field' projective projective' coeffs coeffs' cubic cubic' smooth smooth'
      basePoint basePoint' fieldLedger fieldLedger' projectiveLedger projectiveLedger'
      provenance provenance' : BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      hsame field field' ->
        hsame projective projective' ->
          hsame coeffs coeffs' ->
            hsame cubic cubic' ->
              hsame smooth smooth' ->
                hsame basePoint basePoint' ->
                  Cont field' projective' fieldLedger' ->
                    Cont coeffs' cubic' projectiveLedger' ->
                      Cont smooth' basePoint' provenance' ->
                        EllipticCurveCarrierPacket field' projective' coeffs' cubic' smooth'
                            basePoint' fieldLedger' projectiveLedger' provenance' ∧
                          hsame fieldLedger fieldLedger' ∧
                            hsame projectiveLedger projectiveLedger' ∧
                              hsame provenance provenance' := by
  intro packet sameField sameProjective sameCoeffs sameCubic sameSmooth sameBasePoint
    fieldLedgerCont' projectiveLedgerCont' provenanceCont'
  have fieldUnary' : UnaryHistory field' :=
    unary_transport packet.left sameField
  have projectiveUnary' : UnaryHistory projective' :=
    unary_transport packet.right.left sameProjective
  have coeffsUnary' : UnaryHistory coeffs' :=
    unary_transport packet.right.right.left sameCoeffs
  have basePointUnary' : UnaryHistory basePoint' :=
    unary_transport packet.right.right.right.left sameBasePoint
  have sameFieldLedger : hsame fieldLedger fieldLedger' :=
    cont_respects_hsame sameField sameProjective packet.right.right.right.right.left
      fieldLedgerCont'
  have sameProjectiveLedger : hsame projectiveLedger projectiveLedger' :=
    cont_respects_hsame sameCoeffs sameCubic packet.right.right.right.right.right.left
      projectiveLedgerCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSmooth sameBasePoint packet.right.right.right.right.right.right
      provenanceCont'
  constructor
  · exact And.intro fieldUnary'
      (And.intro projectiveUnary'
        (And.intro coeffsUnary'
          (And.intro basePointUnary'
            (And.intro fieldLedgerCont'
              (And.intro projectiveLedgerCont' provenanceCont')))))
  · exact And.intro sameFieldLedger
      (And.intro sameProjectiveLedger sameProvenance)

theorem EllipticCurveCarrierPacket_semantic_name_certificate
    {field projective coeffs cubic smooth basePoint fieldLedger projectiveLedger provenance :
      BHist} :
    EllipticCurveCarrierPacket field projective coeffs cubic smooth basePoint fieldLedger
        projectiveLedger provenance ->
      SemanticNameCert
        (fun endpoint : BHist =>
          exists carriedBase : BHist, exists carriedProvenance : BHist,
            EllipticCurveCarrierPacket field projective coeffs cubic smooth carriedBase
              fieldLedger projectiveLedger carriedProvenance ∧ hsame endpoint carriedBase)
        (fun endpoint : BHist =>
          exists carriedBase : BHist, exists carriedProvenance : BHist,
            EllipticCurveCarrierPacket field projective coeffs cubic smooth carriedBase
              fieldLedger projectiveLedger carriedProvenance ∧ hsame endpoint carriedBase)
        (fun endpoint : BHist =>
          exists carriedBase : BHist, exists carriedProvenance : BHist,
            EllipticCurveCarrierPacket field projective coeffs cubic smooth carriedBase
              fieldLedger projectiveLedger carriedProvenance ∧ hsame endpoint carriedBase)
        (fun left right : BHist =>
          (exists lb : BHist, exists lp : BHist,
            EllipticCurveCarrierPacket field projective coeffs cubic smooth lb
              fieldLedger projectiveLedger lp ∧ hsame left lb) ∧
          (exists rb : BHist, exists rp : BHist,
            EllipticCurveCarrierPacket field projective coeffs cubic smooth rb
              fieldLedger projectiveLedger rp ∧ hsame right rb) ∧ hsame left right) := by
  intro packet
  constructor
  · constructor
    · refine Exists.intro basePoint ?_
      refine Exists.intro basePoint ?_
      refine Exists.intro provenance ?_
      exact And.intro packet (hsame_refl basePoint)
    · intro endpoint source
      exact And.intro source (And.intro source (hsame_refl endpoint))
    · intro left right same
      exact And.intro same.right.left
        (And.intro same.left (hsame_symm same.right.right))
    · intro left middle right sameLeftMiddle sameMiddleRight
      exact And.intro sameLeftMiddle.left
        (And.intro sameMiddleRight.right.left
          (hsame_trans sameLeftMiddle.right.right sameMiddleRight.right.right))
    · intro left right same _source
      exact same.right.left
  · intro endpoint source
    exact source
  · intro endpoint source
    exact source

end BEDC.Derived.EllipticCurveUp
