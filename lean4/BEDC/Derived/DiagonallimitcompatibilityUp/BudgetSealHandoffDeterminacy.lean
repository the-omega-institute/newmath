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

theorem DiagonalLimitCompatibility_budget_seal_handoff_determinacy
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix sealBudget endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows budgetPrefix →
        Cont budgetPrefix sealRow sealBudget →
          Cont readback realSeal endpoint →
            PkgSig bundle sealBudget pkg →
              PkgSig bundle endpoint pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                        readback realSeal transport route provenance cert bundle pkg ∧
                      hsame row sealBudget)
                  (fun row : BHist =>
                    Cont dyadic windows budgetPrefix ∧ Cont budgetPrefix sealRow row ∧
                      Cont readback realSeal endpoint ∧ PkgSig bundle endpoint pkg)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle sealBudget pkg ∧
                      PkgSig bundle endpoint pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle SemanticNameCert UnaryHistory hsame
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackEndpoint sealBudgetPkg
    endpointPkg
  have carrierFull :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg :=
    carrier
  obtain ⟨_diagonalUnary, _triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _carrierDyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealUnary budgetPrefixSealRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealBudget (And.intro carrierFull (hsame_refl sealBudget))
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
      cases source.right
      exact
        And.intro dyadicWindowsBudgetPrefix
          (And.intro budgetPrefixSealRow (And.intro readbackEndpoint endpointPkg))
    ledger_sound := by
      intro row source
      cases source.right
      exact And.intro sealBudgetUnary (And.intro sealBudgetPkg endpointPkg)
  }

theorem DiagonalLimitCompatibilityBudgetSealHandoffDeterminacy [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix mesh sealBudget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetPrefix ->
        Cont budgetPrefix windows mesh ->
          Cont mesh sealRow sealBudget ->
            Cont sealBudget realSeal terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory budgetPrefix ∧ UnaryHistory mesh ∧ UnaryHistory sealBudget ∧
                  UnaryHistory terminal ∧ Cont diagonal dyadic budgetPrefix ∧
                    Cont budgetPrefix windows mesh ∧ Cont mesh sealRow sealBudget ∧
                      Cont sealBudget realSeal terminal ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicBudget budgetWindowsMesh meshSealBudget sealBudgetTerminal
    terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed budgetUnary windowsUnary budgetWindowsMesh
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed meshUnary sealRowUnary meshSealBudget
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealBudgetUnary realSealUnary sealBudgetTerminal
  exact
    ⟨budgetUnary, meshUnary, sealBudgetUnary, terminalUnary, diagonalDyadicBudget,
      budgetWindowsMesh, meshSealBudget, sealBudgetTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
