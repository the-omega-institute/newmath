import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_terminal_branch_exhaustion [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      prefixRead terminal branchA branchB branchC : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows prefixRead ->
        Cont prefixRead readback terminal ->
          UnaryHistory branchA ->
            Cont terminal branchA branchB ->
              Cont terminal branchB branchC ->
                PkgSig bundle terminal pkg ->
                  PkgSig bundle branchC pkg ->
                    UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory prefixRead ∧
                      UnaryHistory readback ∧ UnaryHistory terminal ∧ UnaryHistory branchA ∧
                        UnaryHistory branchB ∧ UnaryHistory branchC ∧
                          Cont diagonal windows prefixRead ∧
                            Cont prefixRead readback terminal ∧
                              Cont terminal branchA branchB ∧
                                Cont terminal branchB branchC ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle terminal pkg ∧
                                      PkgSig bundle branchC pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsPrefix prefixReadbackTerminal branchAUnary
    terminalBranchA terminalBranchB terminalPkg branchCPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsPrefix
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed prefixUnary readbackUnary prefixReadbackTerminal
  have branchBUnary : UnaryHistory branchB :=
    unary_cont_closed terminalUnary branchAUnary terminalBranchA
  have branchCUnary : UnaryHistory branchC :=
    unary_cont_closed terminalUnary branchBUnary terminalBranchB
  exact
    ⟨diagonalUnary, windowsUnary, prefixUnary, readbackUnary, terminalUnary, branchAUnary,
      branchBUnary, branchCUnary, diagonalWindowsPrefix, prefixReadbackTerminal,
      terminalBranchA, terminalBranchB, provenancePkg, terminalPkg, branchCPkg⟩

theorem DiagonalLimitCompatibilityTerminalBranchExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminalRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont realSeal cert terminalRead ->
        Cont terminalRead route branchRead ->
          PkgSig bundle branchRead pkg ->
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory terminalRead ∧ UnaryHistory branchRead ∧
                  Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                    Cont readback realSeal route ∧ Cont realSeal cert terminalRead ∧
                      Cont terminalRead route branchRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle branchRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier realSealCertTerminal terminalReadRouteBranch branchReadPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute, _routeCertTransport,
    provenancePkg⟩ := carrier
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed realSealUnary certUnary realSealCertTerminal
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed terminalReadUnary routeUnary terminalReadRouteBranch
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, terminalReadUnary, branchReadUnary, diagonalTriangleSeal,
      dyadicWindowsReadback, readbackRealSealRoute, realSealCertTerminal,
      terminalReadRouteBranch, provenancePkg, branchReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
