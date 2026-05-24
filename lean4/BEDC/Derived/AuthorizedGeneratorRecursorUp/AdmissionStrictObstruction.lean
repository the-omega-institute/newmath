import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAdmissionStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont G N refusalRead ->
        PkgSig bundle refusalRead pkg ->
          UnaryHistory G /\ UnaryHistory N /\ UnaryHistory refusalRead /\
            Cont G N refusalRead /\ PkgSig bundle P pkg /\
              PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier refusalCont refusalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, _unaryA, _unaryH,
      _unaryC, unaryP, unaryG, unaryN, _iem, _mbd, _doa, _sameTransport,
      provenancePkg⟩
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryG unaryN refusalCont
  exact ⟨unaryG, unaryN, refusalUnary, refusalCont, provenancePkg, refusalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
