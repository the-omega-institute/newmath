import BEDC.Derived.RealOneUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealOneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealOneTerminalSealNonescape [AskSetup] [PackageSetup]
    {q S R D E C P N streamRead regRead dyadicRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q -> UnaryHistory S -> UnaryHistory R -> UnaryHistory D ->
      UnaryHistory E -> UnaryHistory C -> UnaryHistory N ->
        Cont q S streamRead -> Cont streamRead R regRead ->
          Cont regRead D dyadicRead -> Cont dyadicRead E sealRead ->
            Cont sealRead C namedRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
              UnaryHistory streamRead ∧ UnaryHistory regRead ∧ UnaryHistory dyadicRead ∧
                UnaryHistory sealRead ∧ UnaryHistory namedRead ∧ Cont dyadicRead E sealRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro qUnary sUnary rUnary dUnary eUnary cUnary nUnary streamRoute regularRoute
    dyadicRoute sealRoute namedRoute provenancePkg namePkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed qUnary sUnary streamRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed streamUnary rUnary regularRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary cUnary namedRoute
  exact
    ⟨streamUnary, regUnary, dyadicUnary, sealUnary, namedUnary, sealRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.RealOneUp
