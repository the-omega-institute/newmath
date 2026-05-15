import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorWindowTailSealBridge [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selector' locked locked' tail tail' terminal terminal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont diagonal windows selector' ->
          hsame selector selector' ->
            Cont selector readback locked ->
              Cont selector' readback locked' ->
                Cont locked realSeal tail ->
                  Cont locked' realSeal tail' ->
                    Cont tail sealRow terminal ->
                      Cont tail' sealRow terminal' ->
                        PkgSig bundle terminal pkg ->
                          PkgSig bundle terminal' pkg ->
                            hsame locked locked' ∧ hsame tail tail' ∧
                              hsame terminal terminal' ∧ UnaryHistory locked ∧
                                UnaryHistory locked' ∧ UnaryHistory tail ∧
                                  UnaryHistory tail' ∧ UnaryHistory terminal ∧
                                    UnaryHistory terminal' ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier diagonalWindowsSelector diagonalWindowsSelector' sameSelector
    selectorReadbackLocked selectorReadbackLocked' lockedRealSealTail
    lockedRealSealTail' tailSealTerminal tailSealTerminal' _terminalPkg
    _terminalPkg'
  obtain ⟨diagonalUnary, _triangleUnary, sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have lockedSame : hsame locked locked' :=
    cont_respects_hsame sameSelector (hsame_refl readback) selectorReadbackLocked
      selectorReadbackLocked'
  have tailSame : hsame tail tail' :=
    cont_respects_hsame lockedSame (hsame_refl realSeal) lockedRealSealTail
      lockedRealSealTail'
  have terminalSame : hsame terminal terminal' :=
    cont_respects_hsame tailSame (hsame_refl sealRow) tailSealTerminal
      tailSealTerminal'
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have selectorUnary' : UnaryHistory selector' :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector'
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have lockedUnary' : UnaryHistory locked' :=
    unary_cont_closed selectorUnary' readbackUnary selectorReadbackLocked'
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealTail
  have tailUnary' : UnaryHistory tail' :=
    unary_cont_closed lockedUnary' realSealUnary lockedRealSealTail'
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed tailUnary sealUnary tailSealTerminal
  have terminalUnary' : UnaryHistory terminal' :=
    unary_cont_closed tailUnary' sealUnary tailSealTerminal'
  exact
    ⟨lockedSame, tailSame, terminalSame, lockedUnary, lockedUnary', tailUnary,
      tailUnary', terminalUnary, terminalUnary', provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
