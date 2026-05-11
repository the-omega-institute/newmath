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

theorem DyadicCompletionWindowPacket_public_regseqrat_real_export [AskSetup] [PackageSetup]
    {dyadic window regularTail realBoundary ledger provenance handoff publicRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionWindowPacket dyadic window regularTail realBoundary ledger provenance
        bundle pkg ->
      Cont window ledger handoff ->
        Cont handoff realBoundary publicRow ->
          PkgSig bundle handoff pkg ->
            PkgSig bundle publicRow pkg ->
              UnaryHistory handoff ∧ UnaryHistory publicRow ∧
                hsame regularTail (append dyadic window) ∧
                  hsame ledger (append regularTail realBoundary) ∧
                    hsame handoff (append window ledger) ∧
                      hsame publicRow (append handoff realBoundary) ∧
                        PkgSig bundle publicRow pkg := by
  intro packet handoffRoute publicRoute _handoffPkg publicPkg
  obtain ⟨_dyadicUnary, windowUnary, _regularTailUnary, realBoundaryUnary, ledgerUnary,
    _provenanceUnary, regularTailRoute, ledgerRoute, _ledgerPkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed windowUnary ledgerUnary handoffRoute
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed handoffUnary realBoundaryUnary publicRoute
  have sameRegularTail : hsame regularTail (append dyadic window) :=
    regularTailRoute
  have sameLedger : hsame ledger (append regularTail realBoundary) :=
    ledgerRoute
  have sameHandoff : hsame handoff (append window ledger) :=
    handoffRoute
  have samePublic : hsame publicRow (append handoff realBoundary) :=
    publicRoute
  exact
    ⟨handoffUnary, publicUnary, sameRegularTail, sameLedger, sameHandoff, samePublic,
      publicPkg⟩

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
  intro tailRow' ledgerRow' _provenanceRow' pkgRow'
  obtain ⟨dyadicUnary, windowUnary, _tailUnary, realBoundaryUnary, _ledgerUnary,
    provenanceUnary, tailRow, ledgerRow, _pkgRow⟩ := packet
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
      provenanceUnary', tailRow', ledgerRow', pkgRow'⟩
  · exact ⟨sameTail, sameLedger⟩

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

theorem DyadicCompletionPacket_constant_embedding [AskSetup] [PackageSetup]
    {q window tail real ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q ->
      UnaryHistory window ->
        UnaryHistory real ->
          UnaryHistory provenance ->
            Cont q window tail ->
              Cont tail real ledger ->
                PkgSig bundle provenance pkg ->
                  DyadicCompletionPacket q window tail real ledger provenance bundle pkg ∧
                    UnaryHistory tail ∧ UnaryHistory ledger ∧
                      hsame tail (append q window) ∧ hsame ledger (append tail real) := by
  intro qUnary windowUnary realUnary provenanceUnary tailRow ledgerRow provenancePkg
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed qUnary windowUnary tailRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed tailUnary realUnary ledgerRow
  exact
    ⟨⟨qUnary, windowUnary, realUnary, provenanceUnary, tailRow, ledgerRow, provenancePkg⟩,
      tailUnary, ledgerUnary, tailRow, ledgerRow⟩

theorem DyadicCompletionPacket_ledger_boundary [AskSetup] [PackageSetup]
    {dyadic window tail real ledger provenance boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionPacket dyadic window tail real ledger provenance bundle pkg ->
      Cont ledger provenance boundary ->
        PkgSig bundle boundary pkg ->
          UnaryHistory ledger ∧ UnaryHistory boundary ∧
            hsame tail (append dyadic window) ∧ hsame ledger (append tail real) ∧
              hsame boundary (append ledger provenance) ∧ PkgSig bundle boundary pkg := by
  intro packet boundaryRow boundaryPkg
  obtain ⟨dyadicUnary, windowUnary, realUnary, provenanceUnary, tailRow, ledgerRow,
    _provenancePkg⟩ := packet
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed dyadicUnary windowUnary tailRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed tailUnary realUnary ledgerRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed ledgerUnary provenanceUnary boundaryRow
  exact
    ⟨ledgerUnary, boundaryUnary, tailRow, ledgerRow, boundaryRow, boundaryPkg⟩

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

theorem DyadicCompletionWindowPacket_finite_window_standard_bridge [AskSetup] [PackageSetup]
    {dyadic window regularTail realBoundary ledger provenance handoff publicRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCompletionWindowPacket dyadic window regularTail realBoundary ledger provenance bundle pkg ->
      Cont window ledger handoff ->
        Cont handoff realBoundary publicRow ->
          PkgSig bundle publicRow pkg ->
            DyadicCompletionFiniteWindowSource publicRow ∧
              DyadicCompletionFiniteWindowPattern handoff ∧
                DyadicCompletionFiniteWindowLedger publicRow ∧
                  hsame publicRow (append handoff realBoundary) ∧ PkgSig bundle publicRow pkg := by
  intro _packet handoffRoute publicRoute publicPkg
  have source : DyadicCompletionFiniteWindowSource publicRow :=
    Exists.intro window
      (Exists.intro ledger
        (Exists.intro handoff
          (Exists.intro realBoundary
            (Exists.intro publicRow
              (And.intro handoffRoute (And.intro publicRoute (hsame_refl publicRow)))))))
  have pattern : DyadicCompletionFiniteWindowPattern handoff :=
    Exists.intro window
      (Exists.intro ledger
        (Exists.intro handoff
          (Exists.intro handoff (And.intro handoffRoute (hsame_refl handoff)))))
  have ledgerRow : DyadicCompletionFiniteWindowLedger publicRow :=
    Exists.intro handoff
      (Exists.intro realBoundary
        (Exists.intro publicRow (And.intro publicRoute (hsame_refl publicRow))))
  exact ⟨source, pattern, ledgerRow, publicRoute, publicPkg⟩

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
