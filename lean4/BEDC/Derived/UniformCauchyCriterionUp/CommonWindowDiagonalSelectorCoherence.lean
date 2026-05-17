import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_common_window_diagonal_selector_coherence
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonal
      refined sealBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      UnaryHistory diagonal →
        Cont windows diagonal refined →
          Cont refined sealRow sealBudget →
            PkgSig bundle sealBudget pkg →
              UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory refined ∧
                UnaryHistory sealBudget ∧ Cont index windows modulus ∧
                  Cont windows diagonal refined ∧ Cont refined sealRow sealBudget ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle sealBudget pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet diagonalUnary windowsDiagonalRefined refinedSealBudget sealBudgetPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, _toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have refinedUnary : UnaryHistory refined :=
    unary_cont_closed windowsUnary diagonalUnary windowsDiagonalRefined
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed refinedUnary sealRowUnary refinedSealBudget
  exact
    ⟨windowsUnary, modulusUnary, refinedUnary, sealBudgetUnary, indexWindowsModulus,
      windowsDiagonalRefined, refinedSealBudget, namePkg, sealBudgetPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
