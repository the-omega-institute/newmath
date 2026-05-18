import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalConsumerReadiness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead N terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
              UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory H ∧
                UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory G ∧ UnaryHistory N ∧
                  UnaryHistory outputRead ∧ UnaryHistory terminalRead ∧ Cont I E M ∧
                    Cont M B D ∧ Cont D O A ∧ Cont O A outputRead ∧
                      Cont outputRead N terminalRead ∧ hsame H (append A C) ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputCont terminalCont terminalPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary unaryN terminalCont
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, outputUnary, terminalUnary, contIEM, contMBD, contDOA, outputCont,
      terminalCont, sameTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
