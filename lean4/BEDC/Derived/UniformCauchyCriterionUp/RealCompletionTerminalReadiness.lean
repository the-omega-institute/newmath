import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_terminal_readiness [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name witness
      selectorRead exitRead terminal hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow witness ->
        Cont witness routes selectorRead ->
          Cont selectorRead name exitRead ->
            Cont exitRead provenance terminal ->
              PkgSig bundle witness pkg ->
                PkgSig bundle selectorRead pkg ->
                  PkgSig bundle terminal pkg ->
                    UnaryHistory terminal /\ Cont tail sealRow witness /\
                      Cont witness routes selectorRead /\ Cont selectorRead name exitRead /\
                        Cont exitRead provenance terminal /\ PkgSig bundle terminal pkg /\
                          (Cont terminal (BHist.e0 hostTail) witness -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealWitness witnessRoutesSelector selectorNameExit exitProvenanceTerminal
    _witnessPkg _selectorPkg terminalPkg
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, routesUnary, provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed tailUnary sealRowUnary tailSealWitness
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed witnessUnary routesUnary witnessRoutesSelector
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed selectorUnary nameUnary selectorNameExit
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed exitUnary provenanceUnary exitProvenanceTerminal
  have witnessTerminal : Cont witness (append routes (append name provenance)) terminal := by
    cases witnessRoutesSelector
    cases selectorNameExit
    exact
      exitProvenanceTerminal.trans
        ((append_assoc (append witness routes) name provenance).trans
          (append_assoc witness routes (append name provenance)))
  exact
    ⟨terminalUnary, tailSealWitness, witnessRoutesSelector, selectorNameExit,
      exitProvenanceTerminal, terminalPkg,
      (fun back =>
        cont_mutual_extension_right_tail_absurd.left witnessTerminal back)⟩

end BEDC.Derived.UniformCauchyCriterionUp
