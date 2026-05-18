import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_selector_uniqueness [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name selectorA
      selectorB terminalA terminalB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tail selectorA ->
        Cont windows tail selectorB ->
          Cont selectorA sealRow terminalA ->
            Cont selectorB sealRow terminalB ->
              PkgSig bundle terminalA pkg ->
                PkgSig bundle terminalB pkg ->
                  UnaryHistory selectorA ∧ UnaryHistory selectorB ∧ UnaryHistory terminalA ∧
                    UnaryHistory terminalB ∧ hsame selectorA selectorB ∧
                      hsame terminalA terminalB ∧ Cont selectorA sealRow terminalA ∧
                        Cont selectorB sealRow terminalB ∧ PkgSig bundle terminalA pkg ∧
                          PkgSig bundle terminalB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet windowsTailSelectorA windowsTailSelectorB selectorASealTerminalA
    selectorBSealTerminalB terminalAPkg terminalBPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have selectorAUnary : UnaryHistory selectorA :=
    unary_cont_closed windowsUnary tailUnary windowsTailSelectorA
  have selectorBUnary : UnaryHistory selectorB :=
    unary_cont_closed windowsUnary tailUnary windowsTailSelectorB
  have terminalAUnary : UnaryHistory terminalA :=
    unary_cont_closed selectorAUnary sealRowUnary selectorASealTerminalA
  have terminalBUnary : UnaryHistory terminalB :=
    unary_cont_closed selectorBUnary sealRowUnary selectorBSealTerminalB
  have sameSelector : hsame selectorA selectorB :=
    cont_respects_hsame (hsame_refl windows) (hsame_refl tail) windowsTailSelectorA
      windowsTailSelectorB
  have sameTerminal : hsame terminalA terminalB :=
    cont_respects_hsame sameSelector (hsame_refl sealRow) selectorASealTerminalA
      selectorBSealTerminalB
  exact
    ⟨selectorAUnary, selectorBUnary, terminalAUnary, terminalBUnary, sameSelector,
      sameTerminal, selectorASealTerminalA, selectorBSealTerminalB, terminalAPkg,
      terminalBPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
