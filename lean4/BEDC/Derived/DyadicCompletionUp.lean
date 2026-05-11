import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicCompletionWindowPacket [AskSetup] [PackageSetup]
    (dyadic window tail realBoundary ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyadic ∧ UnaryHistory window ∧ UnaryHistory tail ∧
    UnaryHistory realBoundary ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      Cont dyadic window tail ∧ Cont tail realBoundary ledger ∧
        Cont ledger provenance provenance ∧ PkgSig bundle ledger pkg

theorem DyadicCompletionWindowPacket_regular_tail_stability [AskSetup] [PackageSetup]
    {dyadic window tail realBoundary ledger provenance dyadic' window' tail' realBoundary'
      ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionWindowPacket dyadic window tail realBoundary ledger provenance bundle pkg ->
      hsame dyadic dyadic' ->
        hsame window window' ->
          hsame realBoundary realBoundary' ->
            hsame provenance provenance' ->
              Cont dyadic' window' tail' ->
                Cont tail' realBoundary' ledger' ->
                  Cont ledger' provenance' provenance' ->
                    PkgSig bundle ledger' pkg ->
                      DyadicCompletionWindowPacket dyadic' window' tail' realBoundary' ledger'
                          provenance' bundle pkg ∧
                        hsame tail tail' ∧ hsame ledger ledger' := by
  intro packet sameDyadic sameWindow sameRealBoundary sameProvenance
  intro tailRow' ledgerRow' provenanceRow' pkgRow'
  obtain ⟨dyadicUnary, windowUnary, _tailUnary, realBoundaryUnary, _ledgerUnary,
    provenanceUnary, tailRow, ledgerRow, _provenanceRow, _pkgRow⟩ := packet
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have realBoundaryUnary' : UnaryHistory realBoundary' :=
    unary_transport realBoundaryUnary sameRealBoundary
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have tailUnary' : UnaryHistory tail' :=
    unary_cont_closed dyadicUnary' windowUnary' tailRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed tailUnary' realBoundaryUnary' ledgerRow'
  have sameTail : hsame tail tail' :=
    cont_respects_hsame sameDyadic sameWindow tailRow tailRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTail sameRealBoundary ledgerRow ledgerRow'
  constructor
  · exact ⟨dyadicUnary', windowUnary', tailUnary', realBoundaryUnary', ledgerUnary',
      provenanceUnary', tailRow', ledgerRow', provenanceRow', pkgRow'⟩
  · exact ⟨sameTail, sameLedger⟩

end BEDC.Derived.DyadicCompletionUp
