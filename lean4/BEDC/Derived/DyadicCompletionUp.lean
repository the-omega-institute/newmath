import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def DyadicCompletionPacket [AskSetup] [PackageSetup]
    (dyadic window tail real ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyadic ∧ UnaryHistory window ∧ UnaryHistory real ∧
    UnaryHistory provenance ∧ Cont dyadic window tail ∧ Cont tail real ledger ∧
      PkgSig bundle provenance pkg

theorem DyadicCompletionPacket_regular_tail_stability [AskSetup] [PackageSetup]
    {dyadic window tail real ledger provenance dyadic' window' tail' real' ledger'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionPacket dyadic window tail real ledger provenance bundle pkg ->
      hsame dyadic dyadic' ->
        hsame window window' ->
          hsame real real' ->
            hsame provenance provenance' ->
              Cont dyadic' window' tail' ->
                Cont tail' real' ledger' ->
                  PkgSig bundle provenance' pkg ->
                    DyadicCompletionPacket dyadic' window' tail' real' ledger' provenance'
                        bundle pkg ∧
                      UnaryHistory tail' ∧ UnaryHistory ledger' ∧
                        hsame tail tail' ∧ hsame ledger ledger' := by
  intro packet sameDyadic sameWindow sameReal sameProvenance tailRow' ledgerRow'
    provenancePkg'
  obtain ⟨dyadicUnary, windowUnary, realUnary, _provenanceUnary, tailRow, ledgerRow,
    _provenancePkg⟩ := packet
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have realUnary' : UnaryHistory real' :=
    unary_transport realUnary sameReal
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport _provenanceUnary sameProvenance
  have tailUnary' : UnaryHistory tail' :=
    unary_cont_closed dyadicUnary' windowUnary' tailRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed tailUnary' realUnary' ledgerRow'
  have sameTail : hsame tail tail' :=
    cont_respects_hsame sameDyadic sameWindow tailRow tailRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTail sameReal ledgerRow ledgerRow'
  exact
    And.intro
      (And.intro dyadicUnary'
        (And.intro windowUnary'
          (And.intro realUnary'
            (And.intro provenanceUnary'
              (And.intro tailRow' (And.intro ledgerRow' provenancePkg'))))))
      (And.intro tailUnary'
        (And.intro ledgerUnary' (And.intro sameTail sameLedger)))

end BEDC.Derived.DyadicCompletionUp
