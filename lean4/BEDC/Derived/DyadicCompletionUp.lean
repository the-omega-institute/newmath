import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicCompletionWindowCarrier [AskSetup] [PackageSetup]
    (dyadic windows tail realBoundary ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory tail ∧
    UnaryHistory realBoundary ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      Cont dyadic windows tail ∧ Cont tail realBoundary ledger ∧
        Cont ledger windows provenance ∧ PkgSig bundle provenance pkg

theorem DyadicCompletionWindowCarrier_regular_tail_stability [AskSetup] [PackageSetup]
    {dyadic windows tail realBoundary ledger provenance dyadic' windows' tail' realBoundary'
      ledger' provenance' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionWindowCarrier dyadic windows tail realBoundary ledger provenance bundle pkg ->
      hsame dyadic dyadic' ->
        hsame windows windows' ->
          hsame realBoundary realBoundary' ->
            Cont dyadic' windows' tail' ->
              Cont tail' realBoundary' ledger' ->
                Cont ledger' windows' provenance' ->
                  PkgSig bundle provenance' pkg ->
                    DyadicCompletionWindowCarrier dyadic' windows' tail' realBoundary'
                        ledger' provenance' bundle pkg ∧
                      hsame tail tail' ∧ hsame ledger ledger' ∧
                        hsame provenance provenance' := by
  intro carrier sameDyadic sameWindows sameBoundary tailRow ledgerRow provenanceRow pkgSig
  have dyadicUnary : UnaryHistory dyadic' :=
    unary_transport carrier.left sameDyadic
  have windowsUnary : UnaryHistory windows' :=
    unary_transport carrier.right.left sameWindows
  have boundaryUnary : UnaryHistory realBoundary' :=
    unary_transport carrier.right.right.right.left sameBoundary
  have sameTail : hsame tail tail' :=
    cont_respects_hsame sameDyadic sameWindows
      carrier.right.right.right.right.right.right.left tailRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTail sameBoundary
      carrier.right.right.right.right.right.right.right.left ledgerRow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameWindows
      carrier.right.right.right.right.right.right.right.right.left provenanceRow
  have tailUnary : UnaryHistory tail' :=
    unary_cont_closed dyadicUnary windowsUnary tailRow
  have ledgerUnary : UnaryHistory ledger' :=
    unary_cont_closed tailUnary boundaryUnary ledgerRow
  have provenanceUnary : UnaryHistory provenance' :=
    unary_cont_closed ledgerUnary windowsUnary provenanceRow
  exact And.intro
    (And.intro dyadicUnary
      (And.intro windowsUnary
        (And.intro tailUnary
          (And.intro boundaryUnary
            (And.intro ledgerUnary
              (And.intro provenanceUnary
                (And.intro tailRow (And.intro ledgerRow (And.intro provenanceRow pkgSig)))))))))
    (And.intro sameTail (And.intro sameLedger sameProvenance))

end BEDC.Derived.DyadicCompletionUp
