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

theorem DiagonalLimitCompatibilityCompletionConsumerPackage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootSelector sealSync completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootSelector ->
        Cont rootSelector readback sealSync ->
          Cont sealSync cert completion ->
            PkgSig bundle completion pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                      readback realSeal transport route provenance cert bundle pkg ∧
                    hsame row completion)
                (fun row : BHist =>
                  Cont diagonal dyadic rootSelector ∧ Cont rootSelector readback sealSync ∧
                    Cont sealSync cert row ∧ PkgSig bundle completion pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completion pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig ProbeBundle SemanticNameCert
  intro carrier diagonalDyadicRoot rootReadbackSeal sealCertCompletion completionPkg
  have carrierFull :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg :=
    carrier
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, _windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootSelector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  have sealSyncUnary : UnaryHistory sealSync :=
    unary_cont_closed rootUnary readbackUnary rootReadbackSeal
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed sealSyncUnary certUnary sealCertCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completion (And.intro carrierFull (hsame_refl completion))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        And.intro diagonalDyadicRoot
          (And.intro rootReadbackSeal
            (And.intro
              (cont_result_hsame_transport sealCertCompletion (hsame_symm source.right))
              completionPkg))
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport completionUnary (hsame_symm source.right))
        completionPkg
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
