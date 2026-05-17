import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityStandardBridgeSurface [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont route cert support →
        PkgSig bundle support pkg →
          SemanticNameCert
              (fun row : BHist =>
                DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                  readback realSeal transport route provenance cert bundle pkg ∧
                    hsame row support)
              (fun row : BHist =>
                Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal route ∧ Cont route cert row ∧
                    PkgSig bundle support pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle support pkg)
              hsame ∧
            UnaryHistory support := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeCertSupport supportPkg
  have carrierFull :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg :=
    carrier
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute, _routeCertTransport,
    _provenancePkg⟩ := carrier
  have supportUnary : UnaryHistory support :=
    unary_cont_closed routeUnary certUnary routeCertSupport
  have certCore :
      NameCert
        (fun row : BHist =>
          DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
            realSeal transport route provenance cert bundle pkg ∧ hsame row support)
        hsame := by
    exact {
      carrier_inhabited :=
        Exists.intro support (And.intro carrierFull (hsame_refl support))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
              realSeal transport route provenance cert bundle pkg ∧ hsame row support)
          (fun row : BHist =>
            Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
              Cont readback realSeal route ∧ Cont route cert row ∧ PkgSig bundle support pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle support pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row source
        cases source.right
        exact
          ⟨diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
            routeCertSupport, supportPkg⟩
      ledger_sound := by
        intro row source
        cases source.right
        exact ⟨supportUnary, supportPkg⟩
    }
  exact ⟨semantic, supportUnary⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
