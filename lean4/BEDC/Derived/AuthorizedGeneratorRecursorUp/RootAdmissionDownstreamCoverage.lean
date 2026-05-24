import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootAdmissionDownstreamCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont branchRead D descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead N consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory branchRead /\ UnaryHistory descentRead /\
                  UnaryHistory outputRead /\ UnaryHistory consumerRead /\
                    Cont I E branchRead /\ Cont branchRead D descentRead /\
                      Cont descentRead O outputRead /\ Cont outputRead N consumerRead /\
                        hsame H (append A C) /\ PkgSig bundle P pkg /\
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier branchCont descentCont outputCont consumerCont consumerPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH,
      _unaryC, unaryP, _unaryG, unaryN, _iem, _mbd, _doa, sameTransport,
      provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchCont
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryD descentCont
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO outputCont
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputUnary unaryN consumerCont
  exact
    ⟨branchUnary, descentUnary, outputUnary, consumerUnary, branchCont, descentCont,
      outputCont, consumerCont, sameTransport, provenancePkg, consumerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
