import BEDC.Derived.DiagonallimitcompatibilityUp.RootConsumerNonescape
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_support_projection_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetWindow selectorRoute sealEndpoint supportProjection : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetWindow →
        Cont budgetWindow windows selectorRoute →
          Cont selectorRoute readback sealEndpoint →
            Cont sealEndpoint cert supportProjection →
              PkgSig bundle supportProjection pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                        readback realSeal transport route provenance cert bundle pkg ∧
                      hsame row supportProjection)
                  (fun row : BHist =>
                    Cont diagonal dyadic budgetWindow ∧
                      Cont budgetWindow windows selectorRoute ∧
                        Cont selectorRoute readback sealEndpoint ∧
                          Cont sealEndpoint cert row)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle supportProjection pkg ∧
                      Cont route cert transport)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier diagonalDyadicBudget budgetWindowsSelector selectorReadbackEndpoint
    endpointCertProjection projectionPkg
  have carrierSource := carrier
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, _provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetWindow :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have selectorUnary : UnaryHistory selectorRoute :=
    unary_cont_closed budgetUnary windowsUnary budgetWindowsSelector
  have endpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackEndpoint
  have projectionUnary : UnaryHistory supportProjection :=
    unary_cont_closed endpointUnary certUnary endpointCertProjection
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro supportProjection
          (And.intro carrierSource (hsame_refl supportProjection))
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
    pattern_sound := by
      intro _row source
      exact
        ⟨diagonalDyadicBudget, budgetWindowsSelector, selectorReadbackEndpoint,
          cont_result_hsame_transport endpointCertProjection (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport projectionUnary (hsame_symm source.right), projectionPkg,
          routeCertTransport⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
