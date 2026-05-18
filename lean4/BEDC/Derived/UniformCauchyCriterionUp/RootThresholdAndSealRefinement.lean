import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp.RootThresholdAndSealRefinement

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.UniformCauchyCriterionUp

theorem UniformCauchyCriterionPacket_common_window_diagonal_selector_coherence
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name commonWindow
      diagonalSelector refinedModulus realSealBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows commonWindow →
        Cont commonWindow modulus diagonalSelector →
          Cont diagonalSelector tolerance refinedModulus →
            Cont refinedModulus sealRow realSealBudget →
              PkgSig bundle realSealBudget pkg →
                UnaryHistory commonWindow ∧ UnaryHistory diagonalSelector ∧
                  UnaryHistory refinedModulus ∧ UnaryHistory realSealBudget ∧
                    Cont index windows commonWindow ∧
                      Cont commonWindow modulus diagonalSelector ∧
                        Cont diagonalSelector tolerance refinedModulus ∧
                          Cont refinedModulus sealRow realSealBudget ∧
                            PkgSig bundle name pkg ∧
                              PkgSig bundle realSealBudget pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsCommon commonModulusDiagonal diagonalToleranceRefined
    refinedSealReal realSealPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed indexUnary windowsUnary indexWindowsCommon
  have diagonalSelectorUnary : UnaryHistory diagonalSelector :=
    unary_cont_closed commonWindowUnary modulusUnary commonModulusDiagonal
  have refinedModulusUnary : UnaryHistory refinedModulus :=
    unary_cont_closed diagonalSelectorUnary toleranceUnary diagonalToleranceRefined
  have realSealBudgetUnary : UnaryHistory realSealBudget :=
    unary_cont_closed refinedModulusUnary sealRowUnary refinedSealReal
  exact
    ⟨commonWindowUnary, diagonalSelectorUnary, refinedModulusUnary, realSealBudgetUnary,
      indexWindowsCommon, commonModulusDiagonal, diagonalToleranceRefined, refinedSealReal,
      namePkg, realSealPkg⟩

theorem UniformCauchyCriterionPacket_root_threshold_exhaustion [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows thresholdRead →
        Cont thresholdRead modulus terminalRead →
          PkgSig bundle terminalRead pkg →
            UnaryHistory thresholdRead ∧ UnaryHistory terminalRead ∧
              Cont index windows thresholdRead ∧
                Cont thresholdRead modulus terminalRead ∧
                  Cont index windows modulus ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsThreshold thresholdModulusTerminal terminalReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, _toleranceUnary, _tailUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed thresholdReadUnary modulusUnary thresholdModulusTerminal
  exact
    ⟨thresholdReadUnary, terminalReadUnary, indexWindowsThreshold, thresholdModulusTerminal,
      indexWindowsModulus, namePkg, terminalReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp.RootThresholdAndSealRefinement
