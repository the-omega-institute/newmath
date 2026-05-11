import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModularArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModularArithmeticResidueCarrier [AskSetup] [PackageSetup]
    (modulus witness representative residueLedger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory modulus ∧ UnaryHistory witness ∧ UnaryHistory representative ∧
    UnaryHistory residueLedger ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
      Cont modulus witness residueLedger ∧ Cont representative residueLedger provenance ∧
        Cont provenance witness endpoint ∧ PkgSig bundle endpoint pkg

theorem ModularArithmeticResidueCarrier_stability [AskSetup] [PackageSetup]
    {modulus modulus' witness witness' representative representative' residueLedger residueLedger'
      provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueCarrier modulus witness representative residueLedger provenance
        endpoint bundle pkg ->
      hsame modulus modulus' ->
        hsame witness witness' ->
          hsame representative representative' ->
            Cont modulus' witness' residueLedger' ->
              Cont representative' residueLedger' provenance' ->
                Cont provenance' witness' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    ModularArithmeticResidueCarrier modulus' witness' representative'
                        residueLedger' provenance' endpoint' bundle pkg ∧
                      hsame residueLedger residueLedger' ∧ hsame provenance provenance' ∧
                        hsame endpoint endpoint' := by
  intro carrier sameModulus sameWitness sameRepresentative residueLedgerCont'
    provenanceCont' endpointCont' endpointPkg'
  obtain ⟨modulusUnary, witnessUnary, representativeUnary, _residueLedgerUnary,
    _provenanceUnary, _endpointUnary, residueLedgerCont, provenanceCont, endpointCont,
    _endpointPkg⟩ := carrier
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have witnessUnary' : UnaryHistory witness' :=
    unary_transport witnessUnary sameWitness
  have representativeUnary' : UnaryHistory representative' :=
    unary_transport representativeUnary sameRepresentative
  have sameResidueLedger : hsame residueLedger residueLedger' :=
    cont_respects_hsame sameModulus sameWitness residueLedgerCont residueLedgerCont'
  have residueLedgerUnary' : UnaryHistory residueLedger' :=
    unary_cont_closed modulusUnary' witnessUnary' residueLedgerCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRepresentative sameResidueLedger provenanceCont provenanceCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed representativeUnary' residueLedgerUnary' provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameWitness endpointCont endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' witnessUnary' endpointCont'
  exact
    ⟨⟨modulusUnary', witnessUnary', representativeUnary', residueLedgerUnary',
        provenanceUnary', endpointUnary', residueLedgerCont', provenanceCont', endpointCont',
        endpointPkg'⟩,
      sameResidueLedger, sameProvenance, sameEndpoint⟩

end BEDC.Derived.ModularArithmeticUp
