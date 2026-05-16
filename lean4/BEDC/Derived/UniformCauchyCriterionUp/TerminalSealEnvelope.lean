import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_seal_envelope [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      tailRead sealRead terminalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead terminalRead ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory tail ∧
                  UnaryHistory windowRead ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory terminalRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index windows windowRead ∧
                        Cont windowRead tail tailRead ∧ Cont tail sealRow sealRead ∧
                          Cont tailRead sealRead terminalRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle terminalRead pkg ∧
                              (Cont terminalRead (BHist.e0 hostTail) tailRead -> False) ∧
                                (Cont terminalRead (BHist.e1 hostTail) sealRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet indexWindowsRead windowTailRead tailSealRead tailReadSealTerminal terminalPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowReadUnary tailUnary windowTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealUnary tailSealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailReadSealTerminal
  have sealTailCanonical : Cont sealRead tailRead (append sealRead tailRead) :=
    cont_intro rfl
  have terminalSameCanonical : hsame terminalRead (append sealRead tailRead) :=
    unary_cont_comm tailReadUnary sealReadUnary tailReadSealTerminal sealTailCanonical
  have sealTailTerminal : Cont sealRead tailRead terminalRead :=
    cont_result_hsame_transport sealTailCanonical (hsame_symm terminalSameCanonical)
  have noE0 : Cont terminalRead (BHist.e0 hostTail) tailRead -> False := by
    intro visibleTail
    exact (cont_mutual_extension_left_tail_absurd).left visibleTail tailReadSealTerminal
  have noE1 : Cont terminalRead (BHist.e1 hostTail) sealRead -> False := by
    intro visibleTail
    exact (cont_mutual_extension_left_tail_absurd).right visibleTail sealTailTerminal
  exact
    ⟨indexUnary, windowsUnary, tailUnary, windowReadUnary, tailReadUnary, sealReadUnary,
      terminalReadUnary, indexWindowsModulus, modulusToleranceTail, indexWindowsRead,
      windowTailRead, tailSealRead, tailReadSealTerminal, namePkg, terminalPkg, noE0, noE1⟩

end BEDC.Derived.UniformCauchyCriterionUp
