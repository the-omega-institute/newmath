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

def BitVectorCarrier [AskSetup] [PackageSetup]
    (length spine ledger provenance payload : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧
    Cont length spine payload ∧ Cont payload ledger provenance ∧ PkgSig bundle provenance pkg

theorem BitVectorCarrier_hsame_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance payload length' spine' ledger' provenance' payload' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorCarrier length spine ledger provenance payload bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame ledger ledger' ->
            Cont length' spine' payload' ->
              Cont payload' ledger' provenance' ->
                PkgSig bundle provenance' pkg ->
                  BitVectorCarrier length' spine' ledger' provenance' payload' bundle pkg ∧
                    hsame payload payload' ∧ hsame provenance provenance' := by
  intro carrier sameLength sameSpine sameLedger payloadRow' provenanceRow' pkgSig'
  have lengthUnary : UnaryHistory length :=
    carrier.left
  have spineUnary : UnaryHistory spine :=
    carrier.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.left
  have payloadRow : Cont length spine payload :=
    carrier.right.right.right.left
  have provenanceRow : Cont payload ledger provenance :=
    carrier.right.right.right.right.left
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have samePayload : hsame payload payload' :=
    cont_respects_hsame sameLength sameSpine payloadRow payloadRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame samePayload sameLedger provenanceRow provenanceRow'
  exact And.intro
    (And.intro lengthUnary'
      (And.intro spineUnary'
        (And.intro ledgerUnary'
          (And.intro payloadRow'
            (And.intro provenanceRow' pkgSig')))))
    (And.intro samePayload sameProvenance)

end BEDC.Derived.BitVectorUp
