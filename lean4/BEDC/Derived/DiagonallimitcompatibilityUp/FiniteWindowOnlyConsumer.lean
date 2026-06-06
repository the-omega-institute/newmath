import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_finite_window_only_consumer [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      finiteWindow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows finiteWindow →
        Cont finiteWindow readback consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory finiteWindow ∧ UnaryHistory consumer ∧
                  Cont diagonal triangle sealRow ∧ Cont dyadic windows finiteWindow ∧
                    Cont finiteWindow readback consumer ∧ Cont dyadic windows readback ∧
                      Cont readback realSeal route ∧ Cont route cert transport ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsFinite finiteReadbackConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have finiteWindowUnary : UnaryHistory finiteWindow :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsFinite
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed finiteWindowUnary readbackUnary finiteReadbackConsumer
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, finiteWindowUnary, consumerUnary, diagonalTriangleSeal,
      dyadicWindowsFinite, finiteReadbackConsumer, dyadicWindowsReadback,
      readbackRealSealRoute, routeCertTransport, provenancePkg, consumerPkg⟩

theorem DiagonalLimitCompatibilityFiniteWindowOnlyConsumer [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      windowRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows windowRead ->
        Cont windowRead readback terminal ->
          PkgSig bundle terminal pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row windows ∨ hsame row readback ∨
                    hsame row realSeal ∨ hsame row provenance ∨ hsame row terminal)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont dyadic windows windowRead ∧
                    Cont windowRead readback terminal ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle terminal pkg)
                hsame ∧
              UnaryHistory windowRead ∧ UnaryHistory terminal := by
  -- BEDC touchpoint anchor: DiagonalLimitCompatibilityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier dyadicWindowsWindow windowReadbackTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsWindow
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed windowUnary readbackUnary windowReadbackTerminal
  have certPacket :
      SemanticNameCert
          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row windows ∨ hsame row readback ∨
              hsame row realSeal ∨ hsame row provenance ∨ hsame row terminal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic windows windowRead ∧
              Cont windowRead readback terminal ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle terminal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal ⟨hsame_refl terminal, terminalUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicWindowsWindow, windowReadbackTerminal, provenancePkg,
          terminalPkg⟩
  }
  exact ⟨certPacket, windowUnary, terminalUnary⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
