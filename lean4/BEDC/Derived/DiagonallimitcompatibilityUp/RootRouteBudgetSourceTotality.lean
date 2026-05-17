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

theorem DiagonalLimitCompatibility_root_route_budget_source_totality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetSource →
        Cont budgetSource windows terminal →
          PkgSig bundle terminal pkg →
            SemanticNameCert
              (fun row : BHist =>
                DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                  readback realSeal transport route provenance cert bundle pkg ∧
                    hsame row terminal)
              (fun row : BHist =>
                Cont diagonal dyadic budgetSource ∧ Cont budgetSource windows row ∧
                  PkgSig bundle terminal pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminal pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier diagonalDyadicBudgetSource budgetSourceWindowsTerminal terminalPkg
  have carrierWitness := carrier
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetSource
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed budgetSourceUnary windowsUnary budgetSourceWindowsTerminal
  exact {
    core := {
      carrier_inhabited := Exists.intro terminal ⟨carrierWitness, hsame_refl terminal⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨diagonalDyadicBudgetSource,
          cont_result_hsame_transport budgetSourceWindowsTerminal (hsame_symm source.right),
          terminalPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport terminalUnary (hsame_symm source.right), terminalPkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
