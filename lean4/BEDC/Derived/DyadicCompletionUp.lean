import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def DyadicCompletionFiniteWindowSource (row : BHist) : Prop :=
  exists left right midpoint refinement endpoint : BHist,
    Cont left right midpoint ∧
      Cont midpoint refinement endpoint ∧ hsame row endpoint

def DyadicCompletionFiniteWindowPattern (row : BHist) : Prop :=
  exists left right midpoint endpoint : BHist,
    Cont left right midpoint ∧ hsame row endpoint

def DyadicCompletionFiniteWindowLedger (row : BHist) : Prop :=
  exists midpoint refinement endpoint : BHist,
    Cont midpoint refinement endpoint ∧ hsame row endpoint

theorem DyadicCompletionPacket_namecert_obligation_surface :
    SemanticNameCert DyadicCompletionFiniteWindowSource DyadicCompletionFiniteWindowPattern
      DyadicCompletionFiniteWindowLedger hsame := by
  have source : DyadicCompletionFiniteWindowSource BHist.Empty := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (And.intro (cont_left_unit BHist.Empty)
                (And.intro (cont_left_unit BHist.Empty) (hsame_refl BHist.Empty)))))))
  constructor
  · constructor
    · exact Exists.intro BHist.Empty source
    · intro row _source
      exact hsame_refl row
    · intro left right sameRows
      exact hsame_symm sameRows
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right sameRows sourceLeft
      cases sourceLeft with
      | intro leftWindow leftData =>
          cases leftData with
          | intro rightWindow rightData =>
              cases rightData with
              | intro midpoint midpointData =>
                  cases midpointData with
                  | intro refinement refinementData =>
                      cases refinementData with
                      | intro endpoint packet =>
                          exact Exists.intro leftWindow
                            (Exists.intro rightWindow
                              (Exists.intro midpoint
                                (Exists.intro refinement
                                  (Exists.intro endpoint
                                    (And.intro packet.left
                                      (And.intro packet.right.left
                                        (hsame_trans (hsame_symm sameRows)
                                          packet.right.right)))))))
  · intro row sourceRow
    cases sourceRow with
    | intro left leftData =>
        cases leftData with
        | intro right rightData =>
            cases rightData with
            | intro midpoint midpointData =>
                cases midpointData with
                | intro refinement refinementData =>
                    cases refinementData with
                    | intro endpoint packet =>
                        exact Exists.intro left
                          (Exists.intro right
                            (Exists.intro midpoint
                              (Exists.intro endpoint
                                (And.intro packet.left packet.right.right))))
  · intro row sourceRow
    cases sourceRow with
    | intro left leftData =>
        cases leftData with
        | intro right rightData =>
            cases rightData with
            | intro midpoint midpointData =>
                cases midpointData with
                | intro refinement refinementData =>
                    cases refinementData with
                    | intro endpoint packet =>
                        exact Exists.intro midpoint
                          (Exists.intro refinement
                            (Exists.intro endpoint
                              (And.intro packet.right.left packet.right.right)))

end BEDC.Derived.DyadicCompletionUp
