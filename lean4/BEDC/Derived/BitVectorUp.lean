import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BitVectorBHistSource [AskSetup] [PackageSetup]
    (length spine ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
    Cont length spine endpoint ∧ Cont endpoint ledger provenance ∧ PkgSig bundle provenance pkg

theorem BitVectorBHistSource_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance endpoint length' spine' ledger' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorBHistSource length spine ledger provenance endpoint bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame ledger ledger' ->
            hsame provenance provenance' ->
              Cont length' spine' endpoint' ->
                Cont endpoint' ledger' provenance' ->
                  PkgSig bundle provenance' pkg ->
                    BitVectorBHistSource length' spine' ledger' provenance' endpoint' bundle pkg ∧
                      hsame endpoint endpoint' ∧ hsame provenance provenance' := by
  intro source sameLength sameSpine sameLedger sameProvenance endpointRoute provenanceRoute pkgRoute
  obtain ⟨lengthUnary, spineUnary, ledgerUnary, provenanceUnary, endpointSource,
    provenanceSource, _pkgSource⟩ := source
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameLength sameSpine endpointSource endpointRoute
  have provenanceSameFromRoutes : hsame provenance provenance' :=
    cont_respects_hsame endpointSame sameLedger provenanceSource provenanceRoute
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨lengthUnary', spineUnary', ledgerUnary', provenanceUnary', endpointRoute, provenanceRoute,
        pkgRoute⟩,
      endpointSame, provenanceSameFromRoutes⟩

end BEDC.Derived.BitVectorUp
