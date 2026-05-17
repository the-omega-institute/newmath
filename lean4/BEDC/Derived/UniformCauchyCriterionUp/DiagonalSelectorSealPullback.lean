import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_selector_seal_pullback
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonal
      selector terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows modulus diagonal ->
        Cont diagonal tolerance selector ->
          Cont selector sealRow terminal ->
            PkgSig bundle diagonal pkg ->
              PkgSig bundle selector pkg ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory diagonal ∧ UnaryHistory selector ∧ UnaryHistory terminal ∧
                    Cont windows modulus diagonal ∧ Cont diagonal tolerance selector ∧
                      Cont selector sealRow terminal ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsModulusDiagonal diagonalToleranceSelector selectorSealTerminal
    _diagonalPkg _selectorPkg terminalPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed windowsUnary modulusUnary windowsModulusDiagonal
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary toleranceUnary diagonalToleranceSelector
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectorUnary sealRowUnary selectorSealTerminal
  exact
    ⟨diagonalUnary, selectorUnary, terminalUnary, windowsModulusDiagonal,
      diagonalToleranceSelector, selectorSealTerminal, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
