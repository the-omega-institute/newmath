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
    (dyadic window regularTail realBoundary ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyadic ∧ UnaryHistory window ∧ UnaryHistory regularTail ∧
    UnaryHistory realBoundary ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      Cont dyadic window regularTail ∧ Cont regularTail realBoundary ledger ∧
        PkgSig bundle ledger pkg

theorem DyadicCompletionWindowPacket_streamname_handoff [AskSetup] [PackageSetup]
    {dyadic window regularTail realBoundary ledger provenance handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionWindowPacket dyadic window regularTail realBoundary ledger provenance
        bundle pkg ->
      Cont window ledger handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory dyadic ∧ UnaryHistory window ∧ UnaryHistory regularTail ∧
            UnaryHistory handoff ∧ hsame regularTail (append dyadic window) ∧
              hsame ledger (append regularTail realBoundary) ∧
                hsame handoff (append window ledger) ∧ PkgSig bundle handoff pkg := by
  intro packet handoffRoute handoffPkg
  obtain ⟨dyadicUnary, windowUnary, regularTailUnary, _realBoundaryUnary, ledgerUnary,
    _provenanceUnary, regularTailRoute, ledgerRoute, _ledgerPkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed windowUnary ledgerUnary handoffRoute
  have sameRegularTail : hsame regularTail (append dyadic window) :=
    regularTailRoute
  have sameLedger : hsame ledger (append regularTail realBoundary) :=
    ledgerRoute
  have sameHandoff : hsame handoff (append window ledger) :=
    handoffRoute
  exact
    ⟨dyadicUnary, windowUnary, regularTailUnary, handoffUnary, sameRegularTail,
      sameLedger, sameHandoff, handoffPkg⟩

end BEDC.Derived.DyadicCompletionUp
