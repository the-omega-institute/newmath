import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_selector_seal_exact_pullback [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name selector terminal
      returnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont sealRow transports selector ->
        Cont selector routes terminal ->
          Cont terminal name returnRead ->
            PkgSig bundle selector pkg ->
              PkgSig bundle terminal pkg ->
                PkgSig bundle returnRead pkg ->
                  UnaryHistory selector ∧ UnaryHistory terminal ∧ UnaryHistory returnRead ∧
                    Cont sealRow transports selector ∧ Cont selector routes terminal ∧
                      Cont terminal name returnRead ∧ PkgSig bundle returnRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sealTransportsSelector selectorRoutesTerminal terminalNameReturn
    _selectorPkg _terminalPkg returnPkg
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
    sealRowUnary, transportsUnary, routesUnary, _provenanceUnary, nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed sealRowUnary transportsUnary sealTransportsSelector
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectorUnary routesUnary selectorRoutesTerminal
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed terminalUnary nameUnary terminalNameReturn
  exact
    ⟨selectorUnary, terminalUnary, returnUnary, sealTransportsSelector,
      selectorRoutesTerminal, terminalNameReturn, returnPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
