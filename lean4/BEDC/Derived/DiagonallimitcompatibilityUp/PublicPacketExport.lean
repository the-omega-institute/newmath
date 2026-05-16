import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityPublicPacketExport [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead budgetSeal publicRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
        Cont budgetRoot windows budgetWindow ->
          Cont budgetWindow sealRow budgetRead ->
            Cont budgetRead readback budgetSeal ->
              Cont budgetSeal realSeal publicRead ->
                Cont publicRead cert terminal ->
                  PkgSig bundle terminal pkg ->
                    UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                      UnaryHistory sealRow ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                        UnaryHistory cert ∧ UnaryHistory budgetRoot ∧
                          UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                            UnaryHistory budgetSeal ∧ UnaryHistory publicRead ∧
                              UnaryHistory terminal ∧ Cont diagonal dyadic budgetRoot ∧
                                Cont budgetRoot windows budgetWindow ∧
                                  Cont budgetWindow sealRow budgetRead ∧
                                    Cont budgetRead readback budgetSeal ∧
                                      Cont budgetSeal realSeal publicRead ∧
                                        Cont publicRead cert terminal ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicRoot rootWindowsWindow windowSealRead readReadbackSeal
    sealRealPublic publicCertTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary rootWindowsWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary sealRowUnary windowSealRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary readbackUnary readReadbackSeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed budgetSealUnary realSealUnary sealRealPublic
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed publicReadUnary certUnary publicCertTerminal
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, sealRowUnary, readbackUnary, realSealUnary,
      certUnary, budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary,
      publicReadUnary, terminalUnary, diagonalDyadicRoot, rootWindowsWindow, windowSealRead,
      readReadbackSeal, sealRealPublic, publicCertTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
