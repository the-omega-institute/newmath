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

theorem DiagonalLimitCompatibilityCarrier_selector_budget_route_determinacy
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback locked →
          Cont locked realSeal sealEndpoint →
            PkgSig bundle sealEndpoint pkg →
              SemanticNameCert
                (fun row : BHist =>
                  DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                    readback realSeal transport route provenance cert bundle pkg ∧
                      hsame row sealEndpoint)
                (fun row : BHist =>
                  Cont diagonal windows selector ∧ Cont selector readback locked ∧
                    Cont locked realSeal row ∧ PkgSig bundle sealEndpoint pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealEndpoint pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    endpointPkg
  have carrierWitness :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg :=
    carrier
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have sealEndpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealEndpoint (And.intro carrierWitness (hsame_refl sealEndpoint))
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
        ⟨diagonalWindowsSelector, selectorReadbackLocked,
          cont_result_hsame_transport lockedRealSealEndpoint (hsame_symm source.right),
          endpointPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport sealEndpointUnary (hsame_symm source.right), endpointPkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
