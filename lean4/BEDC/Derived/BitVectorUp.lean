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

def BitVectorSource [AskSetup] [PackageSetup]
    (length spine ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧
    UnaryHistory provenance ∧ Cont length spine ledger ∧ PkgSig bundle provenance pkg

theorem BitVectorSource_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance length' spine' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorSource length spine ledger provenance bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame provenance provenance' ->
            Cont length' spine' ledger' ->
              PkgSig bundle provenance' pkg ->
                BitVectorSource length' spine' ledger' provenance' bundle pkg ∧
                  hsame ledger ledger' := by
  intro source sameLength sameSpine sameProvenance ledgerRow' pkgSig'
  cases source with
  | intro lengthUnary sourceRest =>
      cases sourceRest with
      | intro spineUnary sourceRest =>
          cases sourceRest with
          | intro _ledgerUnary sourceRest =>
              cases sourceRest with
              | intro provenanceUnary sourceRest =>
                  cases sourceRest with
                  | intro ledgerRow _pkgSig =>
                      have lengthUnary' : UnaryHistory length' :=
                        unary_transport lengthUnary sameLength
                      have spineUnary' : UnaryHistory spine' :=
                        unary_transport spineUnary sameSpine
                      have provenanceUnary' : UnaryHistory provenance' :=
                        unary_transport provenanceUnary sameProvenance
                      have ledgerUnary' : UnaryHistory ledger' :=
                        unary_repetition_closed_under_continuation lengthUnary' spineUnary'
                          ledgerRow'
                      have sameLedger : hsame ledger ledger' :=
                        cont_respects_hsame sameLength sameSpine ledgerRow ledgerRow'
                      constructor
                      · exact ⟨lengthUnary', spineUnary', ledgerUnary', provenanceUnary',
                          ledgerRow', pkgSig'⟩
                      · exact sameLedger

end BEDC.Derived.BitVectorUp
