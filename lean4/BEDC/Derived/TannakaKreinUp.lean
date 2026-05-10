import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TannakaKreinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TannakaKreinFiberFunctorCarrier [AskSetup] [PackageSetup]
    (lieGroupSource monoidalCatSource fiberFunctor representationRows tensorUnit tensorProduct
      reconstructionLedger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lieGroupSource ∧ UnaryHistory monoidalCatSource ∧
    UnaryHistory representationRows ∧ UnaryHistory tensorProduct ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont lieGroupSource monoidalCatSource fiberFunctor ∧
          Cont fiberFunctor representationRows tensorUnit ∧
            Cont tensorUnit tensorProduct reconstructionLedger ∧
              Cont reconstructionLedger tensorProduct provenance ∧
                Cont provenance reconstructionLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem TannakaKreinFiberFunctorCarrier_classifier_stability [AskSetup] [PackageSetup]
    {lieGroupSource monoidalCatSource fiberFunctor representationRows tensorUnit tensorProduct
      reconstructionLedger provenance endpoint lieGroupSource' monoidalCatSource'
      fiberFunctor' representationRows' tensorUnit' tensorProduct' reconstructionLedger'
      provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroupSource monoidalCatSource fiberFunctor
        representationRows tensorUnit tensorProduct reconstructionLedger provenance endpoint
        bundle pkg ->
      hsame lieGroupSource lieGroupSource' ->
        hsame monoidalCatSource monoidalCatSource' ->
          hsame representationRows representationRows' ->
            hsame tensorProduct tensorProduct' ->
              Cont lieGroupSource' monoidalCatSource' fiberFunctor' ->
                Cont fiberFunctor' representationRows' tensorUnit' ->
                  Cont tensorUnit' tensorProduct' reconstructionLedger' ->
                    Cont reconstructionLedger' tensorProduct' provenance' ->
                      Cont provenance' reconstructionLedger' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          TannakaKreinFiberFunctorCarrier lieGroupSource' monoidalCatSource'
                              fiberFunctor' representationRows' tensorUnit' tensorProduct'
                              reconstructionLedger' provenance' endpoint' bundle pkg ∧
                            hsame fiberFunctor fiberFunctor' ∧ hsame tensorUnit tensorUnit' ∧
                              hsame reconstructionLedger reconstructionLedger' ∧
                                hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameLieGroup sameMonoidalCat sameRepresentation sameTensorProduct
    fiberFunctorCont tensorUnitCont reconstructionCont provenanceCont endpointCont endpointPkg
  have sameFiberFunctor : hsame fiberFunctor fiberFunctor' :=
    cont_respects_hsame sameLieGroup sameMonoidalCat
      carrier.right.right.right.right.right.right.left fiberFunctorCont
  have sameTensorUnit : hsame tensorUnit tensorUnit' :=
    cont_respects_hsame sameFiberFunctor sameRepresentation
      carrier.right.right.right.right.right.right.right.left tensorUnitCont
  have sameReconstructionLedger : hsame reconstructionLedger reconstructionLedger' :=
    cont_respects_hsame sameTensorUnit sameTensorProduct
      carrier.right.right.right.right.right.right.right.right.left reconstructionCont
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameReconstructionLedger sameTensorProduct
      carrier.right.right.right.right.right.right.right.right.right.left provenanceCont
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameReconstructionLedger
      carrier.right.right.right.right.right.right.right.right.right.right.left endpointCont
  have transportedCarrier :
      TannakaKreinFiberFunctorCarrier lieGroupSource' monoidalCatSource' fiberFunctor'
        representationRows' tensorUnit' tensorProduct' reconstructionLedger' provenance'
        endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameLieGroup,
      unary_transport carrier.right.left sameMonoidalCat,
      unary_transport carrier.right.right.left sameRepresentation,
      unary_transport carrier.right.right.right.left sameTensorProduct,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      unary_transport carrier.right.right.right.right.right.left sameEndpoint,
      fiberFunctorCont,
      tensorUnitCont,
      reconstructionCont,
      provenanceCont,
      endpointCont,
      endpointPkg⟩
  exact And.intro transportedCarrier
    (And.intro sameFiberFunctor
      (And.intro sameTensorUnit
        (And.intro sameReconstructionLedger
          (And.intro sameProvenance sameEndpoint))))

end BEDC.Derived.TannakaKreinUp
