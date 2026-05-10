import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocalFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocalFieldValuedBHistCarrier [AskSetup] [PackageSetup]
    (field valuation residue unit completeness endpoint ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory field ∧ UnaryHistory valuation ∧ UnaryHistory residue ∧
    UnaryHistory unit ∧ UnaryHistory completeness ∧ Cont field valuation endpoint ∧
      Cont residue unit ledger ∧ Cont endpoint ledger provenance ∧ PkgSig bundle provenance pkg

theorem LocalFieldValuationClassifier_stability [AskSetup] [PackageSetup]
    {field valuation residue unit completeness endpoint ledger provenance field' valuation'
      residue' unit' endpoint' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalFieldValuedBHistCarrier field valuation residue unit completeness endpoint ledger
        provenance bundle pkg ->
      hsame field field' -> hsame valuation valuation' -> hsame residue residue' ->
        hsame unit unit' -> Cont field' valuation' endpoint' ->
          Cont residue' unit' ledger' -> Cont endpoint' ledger' provenance' ->
            PkgSig bundle provenance' pkg ->
              LocalFieldValuedBHistCarrier field' valuation' residue' unit' completeness
                  endpoint' ledger' provenance' bundle pkg ∧
                hsame endpoint endpoint' ∧ hsame ledger ledger' ∧ hsame provenance provenance' := by
  intro carrier sameField sameValuation sameResidue sameUnit endpointRow' ledgerRow'
  intro provenanceRow' pkgSig'
  have fieldUnary' : UnaryHistory field' := unary_transport carrier.left sameField
  have valuationUnary' : UnaryHistory valuation' :=
    unary_transport carrier.right.left sameValuation
  have residueUnary' : UnaryHistory residue' :=
    unary_transport carrier.right.right.left sameResidue
  have unitUnary' : UnaryHistory unit' :=
    unary_transport carrier.right.right.right.left sameUnit
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameField sameValuation carrier.right.right.right.right.right.left
      endpointRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameResidue sameUnit carrier.right.right.right.right.right.right.left
      ledgerRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameEndpoint sameLedger
      carrier.right.right.right.right.right.right.right.left provenanceRow'
  exact
    ⟨⟨fieldUnary', valuationUnary', residueUnary', unitUnary',
      carrier.right.right.right.right.left, endpointRow', ledgerRow', provenanceRow', pkgSig'⟩,
      sameEndpoint, sameLedger, sameProvenance⟩

end BEDC.Derived.LocalFieldUp
