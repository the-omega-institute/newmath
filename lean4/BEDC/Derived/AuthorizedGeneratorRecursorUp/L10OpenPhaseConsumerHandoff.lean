import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOpenPhaseConsumerHandoff [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C consumerRead ->
          PkgSig bundle consumerRead pkg ->
            UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory P ∧
              UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory outputRead ∧
                UnaryHistory consumerRead ∧ Cont O A outputRead ∧
                  Cont outputRead C consumerRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputCont consumerCont consumerPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH, unaryC,
      unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, _sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputCont
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputUnary unaryC consumerCont
  exact
    ⟨unaryO, unaryA, unaryC, unaryP, unaryG, unaryN, outputUnary, consumerUnary,
      outputCont, consumerCont, provenancePkg, consumerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
