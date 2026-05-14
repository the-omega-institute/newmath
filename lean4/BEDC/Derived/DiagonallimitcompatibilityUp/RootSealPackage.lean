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

theorem DiagonalLimitCompatibilityRootSealPackage [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          Cont readback realSeal endpoint ->
            PkgSig bundle sealBudget pkg ->
              PkgSig bundle endpoint pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                      readback realSeal transport route provenance cert bundle pkg ∧
                      hsame row endpoint)
                  (fun row : BHist =>
                    Cont dyadic windows budgetPrefix ∧ Cont budgetPrefix sealRow sealBudget ∧
                      Cont readback realSeal row)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealBudget readbackEndpoint
    _sealBudgetPkg endpointPkg
  have carrierWitness := carrier
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  have sourceEndpoint :
      (fun row : BHist =>
        DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
          realSeal transport route provenance cert bundle pkg ∧ hsame row endpoint)
        endpoint := by
    exact And.intro carrierWitness (hsame_refl endpoint)
  have core :
      NameCert
        (fun row : BHist =>
          DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
            realSeal transport route provenance cert bundle pkg ∧ hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowEndpoint : hsame row endpoint := sourceRow.right
        have sameOtherEndpoint : hsame other endpoint :=
          hsame_trans (hsame_symm same) sameRowEndpoint
        exact And.intro sourceRow.left sameOtherEndpoint
    }
  exact {
    core := core
    pattern_sound := by
      intro row sourceRow
      have readbackRow : Cont readback realSeal row :=
        cont_result_hsame_transport readbackEndpoint (hsame_symm sourceRow.right)
      exact ⟨dyadicWindowsBudgetPrefix, budgetPrefixSealBudget, readbackRow⟩
    ledger_sound := by
      intro row sourceRow
      have rowUnary : UnaryHistory row :=
        unary_transport endpointUnary (hsame_symm sourceRow.right)
      exact And.intro rowUnary endpointPkg
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
