import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TannakaKreinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TannakaKreinFiberFunctorCarrier [AskSetup] [PackageSetup]
    (lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lieGroup ∧ UnaryHistory monoidalCat ∧ UnaryHistory fiberFunctor ∧
    UnaryHistory representation ∧ UnaryHistory unitRow ∧
      Cont lieGroup monoidalCat reconstructionLedger ∧
        Cont fiberFunctor representation tensorProduct ∧ Cont unitRow tensorProduct provenance ∧
          Cont provenance reconstructionLedger endpoint ∧ PkgSig bundle endpoint pkg

private theorem TannakaKreinFiberFunctorCarrier_classifier_stability_provenance
    [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint fiberFunctor' representation' unitRow'
      tensorProduct' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      hsame fiberFunctor fiberFunctor' ->
        hsame representation representation' ->
          hsame unitRow unitRow' ->
            Cont fiberFunctor' representation' tensorProduct' ->
              Cont unitRow' tensorProduct' provenance' ->
                hsame provenance provenance' := by
  intro carrier sameFiberFunctor sameRepresentation sameUnitRow tensorProductCont provenanceCont
  have sameTensorProduct : hsame tensorProduct tensorProduct' :=
    cont_respects_hsame sameFiberFunctor sameRepresentation
      carrier.right.right.right.right.right.right.left tensorProductCont
  exact
    cont_respects_hsame sameUnitRow sameTensorProduct
      carrier.right.right.right.right.right.right.right.left provenanceCont

theorem TannakaKreinFiberFunctorCarrier_classifier_stability [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint lieGroup' monoidalCat' fiberFunctor'
      representation' unitRow' tensorProduct' reconstructionLedger' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      hsame lieGroup lieGroup' ->
        hsame monoidalCat monoidalCat' ->
          hsame fiberFunctor fiberFunctor' ->
            hsame representation representation' ->
              hsame unitRow unitRow' ->
                Cont lieGroup' monoidalCat' reconstructionLedger' ->
                  Cont fiberFunctor' representation' tensorProduct' ->
                    Cont unitRow' tensorProduct' provenance' ->
                      Cont provenance' reconstructionLedger' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          TannakaKreinFiberFunctorCarrier lieGroup' monoidalCat'
                              fiberFunctor' representation' unitRow' tensorProduct'
                              reconstructionLedger' provenance' endpoint' bundle pkg ∧
                            hsame tensorProduct tensorProduct' ∧
                              hsame reconstructionLedger reconstructionLedger' ∧
                                hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameLieGroup sameMonoidalCat sameFiberFunctor sameRepresentation sameUnitRow
    reconstructionCont tensorProductCont provenanceCont endpointCont endpointPkg
  have sameReconstructionLedger : hsame reconstructionLedger reconstructionLedger' :=
    cont_respects_hsame sameLieGroup sameMonoidalCat
      carrier.right.right.right.right.right.left reconstructionCont
  have sameTensorProduct : hsame tensorProduct tensorProduct' :=
    cont_respects_hsame sameFiberFunctor sameRepresentation
      carrier.right.right.right.right.right.right.left tensorProductCont
  have sameProvenance : hsame provenance provenance' :=
    TannakaKreinFiberFunctorCarrier_classifier_stability_provenance carrier sameFiberFunctor
      sameRepresentation sameUnitRow tensorProductCont provenanceCont
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameReconstructionLedger
      carrier.right.right.right.right.right.right.right.right.left endpointCont
  have transportedCarrier :
      TannakaKreinFiberFunctorCarrier lieGroup' monoidalCat' fiberFunctor' representation'
        unitRow' tensorProduct' reconstructionLedger' provenance' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameLieGroup,
      unary_transport carrier.right.left sameMonoidalCat,
      unary_transport carrier.right.right.left sameFiberFunctor,
      unary_transport carrier.right.right.right.left sameRepresentation,
      unary_transport carrier.right.right.right.right.left sameUnitRow,
      reconstructionCont,
      tensorProductCont,
      provenanceCont,
      endpointCont,
      endpointPkg⟩
  exact And.intro transportedCarrier
    (And.intro sameTensorProduct
      (And.intro sameReconstructionLedger (And.intro sameProvenance sameEndpoint)))

def TannakaKreinMonoidalClassifier [AskSetup] [PackageSetup]
    (lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint lieGroup' monoidalCat' fiberFunctor'
      representation' unitRow' tensorProduct' reconstructionLedger' provenance'
      endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
      tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
    TannakaKreinFiberFunctorCarrier lieGroup' monoidalCat' fiberFunctor' representation'
        unitRow' tensorProduct' reconstructionLedger' provenance' endpoint' bundle pkg ∧
      hsame lieGroup lieGroup' ∧ hsame monoidalCat monoidalCat' ∧
        hsame fiberFunctor fiberFunctor' ∧ hsame representation representation' ∧
          hsame unitRow unitRow' ∧ hsame tensorProduct tensorProduct' ∧
            hsame reconstructionLedger reconstructionLedger' ∧ hsame provenance provenance' ∧
              hsame endpoint endpoint'

theorem TannakaKreinFiberFunctorCarrier_source_boundary [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      UnaryHistory lieGroup ∧ UnaryHistory monoidalCat ∧ UnaryHistory fiberFunctor ∧
        UnaryHistory representation ∧ UnaryHistory unitRow ∧ UnaryHistory tensorProduct ∧
          UnaryHistory reconstructionLedger ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
            hsame reconstructionLedger (append lieGroup monoidalCat) ∧
              hsame tensorProduct (append fiberFunctor representation) ∧
                hsame provenance (append unitRow tensorProduct) ∧
                  hsame endpoint (append provenance reconstructionLedger) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier
  have lieGroupUnary : UnaryHistory lieGroup := carrier.left
  have monoidalCatUnary : UnaryHistory monoidalCat := carrier.right.left
  have fiberFunctorUnary : UnaryHistory fiberFunctor := carrier.right.right.left
  have representationUnary : UnaryHistory representation := carrier.right.right.right.left
  have unitRowUnary : UnaryHistory unitRow := carrier.right.right.right.right.left
  have reconstructionLedgerCont : Cont lieGroup monoidalCat reconstructionLedger :=
    carrier.right.right.right.right.right.left
  have tensorProductCont : Cont fiberFunctor representation tensorProduct :=
    carrier.right.right.right.right.right.right.left
  have provenanceCont : Cont unitRow tensorProduct provenance :=
    carrier.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance reconstructionLedger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have reconstructionLedgerUnary : UnaryHistory reconstructionLedger :=
    unary_cont_closed lieGroupUnary monoidalCatUnary reconstructionLedgerCont
  have tensorProductUnary : UnaryHistory tensorProduct :=
    unary_cont_closed fiberFunctorUnary representationUnary tensorProductCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed unitRowUnary tensorProductUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary reconstructionLedgerUnary endpointCont
  exact And.intro lieGroupUnary
    (And.intro monoidalCatUnary
      (And.intro fiberFunctorUnary
        (And.intro representationUnary
          (And.intro unitRowUnary
            (And.intro tensorProductUnary
              (And.intro reconstructionLedgerUnary
                (And.intro provenanceUnary
                  (And.intro endpointUnary
                    (And.intro reconstructionLedgerCont
                      (And.intro tensorProductCont
                        (And.intro provenanceCont
                          (And.intro endpointCont pkgSig))))))))))))

theorem TannakaKreinFiberFunctorCarrier_endpoint_deterministic [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      Cont provenance reconstructionLedger endpoint' ->
        PkgSig bundle endpoint' pkg ->
          TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint' bundle pkg ∧
            hsame endpoint endpoint' := by
  intro carrier endpointCont endpointPkg
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_deterministic carrier.right.right.right.right.right.right.right.right.left endpointCont
  have transportedCarrier :
      TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint' bundle pkg :=
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      endpointCont,
      endpointPkg⟩
  exact And.intro transportedCarrier sameEndpoint

theorem TannakaKreinFiberFunctorCarrier_reconstruction_ledger_exactness
    [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      UnaryHistory tensorProduct ∧ UnaryHistory reconstructionLedger ∧
        UnaryHistory provenance ∧ UnaryHistory endpoint ∧
          hsame tensorProduct (append fiberFunctor representation) ∧
            hsame reconstructionLedger (append lieGroup monoidalCat) ∧
              hsame provenance (append unitRow tensorProduct) ∧
                hsame endpoint (append provenance reconstructionLedger) ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier
  have lieGroupUnary : UnaryHistory lieGroup := carrier.left
  have monoidalCatUnary : UnaryHistory monoidalCat := carrier.right.left
  have fiberFunctorUnary : UnaryHistory fiberFunctor := carrier.right.right.left
  have representationUnary : UnaryHistory representation := carrier.right.right.right.left
  have unitRowUnary : UnaryHistory unitRow := carrier.right.right.right.right.left
  have reconstructionLedgerCont : Cont lieGroup monoidalCat reconstructionLedger :=
    carrier.right.right.right.right.right.left
  have tensorProductCont : Cont fiberFunctor representation tensorProduct :=
    carrier.right.right.right.right.right.right.left
  have provenanceCont : Cont unitRow tensorProduct provenance :=
    carrier.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance reconstructionLedger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have tensorProductUnary : UnaryHistory tensorProduct :=
    unary_cont_closed fiberFunctorUnary representationUnary tensorProductCont
  have reconstructionLedgerUnary : UnaryHistory reconstructionLedger :=
    unary_cont_closed lieGroupUnary monoidalCatUnary reconstructionLedgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed unitRowUnary tensorProductUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary reconstructionLedgerUnary endpointCont
  exact
    And.intro tensorProductUnary
      (And.intro reconstructionLedgerUnary
        (And.intro provenanceUnary
          (And.intro endpointUnary
            (And.intro tensorProductCont
              (And.intro reconstructionLedgerCont
                (And.intro provenanceCont (And.intro endpointCont pkgSig)))))))

theorem TannakaKreinFiberFunctorCarrier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
              hsame row endpoint)
          hsame ∧
        UnaryHistory reconstructionLedger ∧ UnaryHistory tensorProduct ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have lieGroupUnary : UnaryHistory lieGroup := carrier.left
  have monoidalCatUnary : UnaryHistory monoidalCat := carrier.right.left
  have fiberFunctorUnary : UnaryHistory fiberFunctor := carrier.right.right.left
  have representationUnary : UnaryHistory representation := carrier.right.right.right.left
  have unitRowUnary : UnaryHistory unitRow := carrier.right.right.right.right.left
  have reconstructionLedgerCont : Cont lieGroup monoidalCat reconstructionLedger :=
    carrier.right.right.right.right.right.left
  have tensorProductCont : Cont fiberFunctor representation tensorProduct :=
    carrier.right.right.right.right.right.right.left
  have provenanceCont : Cont unitRow tensorProduct provenance :=
    carrier.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance reconstructionLedger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have reconstructionLedgerUnary : UnaryHistory reconstructionLedger :=
    unary_cont_closed lieGroupUnary monoidalCatUnary reconstructionLedgerCont
  have tensorProductUnary : UnaryHistory tensorProduct :=
    unary_cont_closed fiberFunctorUnary representationUnary tensorProductCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed unitRowUnary tensorProductUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary reconstructionLedgerUnary endpointCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation
              unitRow tensorProduct reconstructionLedger provenance endpoint bundle pkg ∧
              hsame row endpoint)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    · intro row source
      exact source
    · intro row source
      exact source
  exact
    ⟨cert,
      reconstructionLedgerUnary,
      tensorProductUnary,
      provenanceUnary,
      endpointUnary,
      pkgSig⟩

end BEDC.Derived.TannakaKreinUp
