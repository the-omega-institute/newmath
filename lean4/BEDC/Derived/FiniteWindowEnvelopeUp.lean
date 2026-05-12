import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWindowEnvelopeCarrier [AskSetup] [PackageSetup]
    (source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory anchor ∧ UnaryHistory window ∧ UnaryHistory ledger ∧
    Cont window ledger regSeal ∧ Cont regSeal endpoint streamSeal ∧
      Cont streamSeal localCert provenance ∧ PkgSig bundle provenance pkg

theorem FiniteWindowEnvelopeCarrier_regseqrat_seal_handoff [AskSetup] [PackageSetup]
    {source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeCarrier source anchor window ledger streamSeal regSeal endpoint provenance
        localCert bundle pkg →
      UnaryHistory regSeal ∧ hsame regSeal (append window ledger) ∧
        PkgSig bundle provenance pkg := by
  intro carrier
  have windowUnary : UnaryHistory window :=
    carrier.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.right.left
  have regSealCont : Cont window ledger regSeal :=
    carrier.right.right.right.right.left
  have regSealUnary : UnaryHistory regSeal :=
    unary_cont_closed windowUnary ledgerUnary regSealCont
  have regSealSame : hsame regSeal (append window ledger) :=
    regSealCont
  exact And.intro regSealUnary (And.intro regSealSame carrier.right.right.right.right.right.right.right)

def FiniteWindowEnvelopeBHistCarrier [AskSetup] [PackageSetup]
    (source anchor window ledger streamClass sealRow endpoint provenance nameCert route : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory anchor ∧ UnaryHistory window ∧
    UnaryHistory ledger ∧ UnaryHistory streamClass ∧ UnaryHistory sealRow ∧
      UnaryHistory endpoint ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        UnaryHistory route ∧ hsame sealRow (append ledger streamClass) ∧
          Cont sealRow endpoint route ∧ PkgSig bundle endpoint pkg

theorem FiniteWindowEnvelopeBHistCarrier_regseqrat_seal_handoff [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route source'
      anchor' window' ledger' endpoint' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg ->
      hsame source source' ->
        hsame anchor anchor' ->
          hsame window window' ->
            hsame ledger ledger' ->
              hsame endpoint endpoint' ->
                hsame provenance provenance' ->
                  hsame nameCert nameCert' ->
                    exists streamClass' sealOut route',
                      FiniteWindowEnvelopeBHistCarrier source' anchor' window' ledger'
                          streamClass' sealOut endpoint' provenance' nameCert' route'
                          bundle pkg ∧
                        hsame sealOut (append ledger' streamClass') ∧
                          Cont sealOut endpoint' route' := by
  intro carrier sameSource sameAnchor sameWindow sameLedger sameEndpoint sameProvenance
    sameNameCert
  obtain ⟨sourceUnary, anchorUnary, windowUnary, ledgerUnary, streamClassUnary, _sealUnary,
    endpointUnary, provenanceUnary, nameCertUnary, _routeUnary, _sealEq, _routeRow,
    pkgRow⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have anchorUnary' : UnaryHistory anchor' :=
    unary_transport anchorUnary sameAnchor
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  let streamClass' : BHist := streamClass
  let sealOut : BHist := append ledger' streamClass'
  let route' : BHist := append sealOut endpoint'
  have sealUnary' : UnaryHistory sealOut :=
    unary_cont_closed ledgerUnary' streamClassUnary (rfl : Cont ledger' streamClass' sealOut)
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed sealUnary' endpointUnary' (rfl : Cont sealOut endpoint' route')
  have pkgRow' : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact pkgRow
  exact
    ⟨streamClass', sealOut, route',
      ⟨sourceUnary', anchorUnary', windowUnary', ledgerUnary', streamClassUnary, sealUnary',
        endpointUnary', provenanceUnary', nameCertUnary', routeUnary', rfl, rfl, pkgRow'⟩,
      rfl, rfl⟩

end BEDC.Derived.FiniteWindowEnvelopeUp
