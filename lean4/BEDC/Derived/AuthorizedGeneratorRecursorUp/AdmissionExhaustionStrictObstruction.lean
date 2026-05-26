import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAdmissionExhaustionStrictObstruction [AskSetup]
    [PackageSetup] {I E M B D O A H C P G N refusalRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont G N refusalRead ->
        Cont refusalRead A boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            UnaryHistory G /\ UnaryHistory N /\ UnaryHistory refusalRead /\
              UnaryHistory boundaryRead /\ Cont G N refusalRead /\
                Cont refusalRead A boundaryRead /\ hsame H (append A C) /\
                  PkgSig bundle P pkg /\ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier refusalCont boundaryCont boundaryPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, _iem, _mbd, _doa, transportSame,
      provenancePkg⟩
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryG unaryN refusalCont
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed refusalUnary unaryA boundaryCont
  exact
    ⟨unaryG, unaryN, refusalUnary, boundaryUnary, refusalCont, boundaryCont,
      transportSame, provenancePkg, boundaryPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
