import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedPseudometricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparatedPseudometricCompletionCarrier [AskSetup] [PackageSetup]
    (P Z Q M S R D E H C K N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory P ∧ UnaryHistory Z ∧ UnaryHistory Q ∧ UnaryHistory M ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory N ∧
        PkgSig bundle K pkg ∧ PkgSig bundle N pkg

theorem SeparatedPseudometricCompletionCarrier_completion_route [AskSetup] [PackageSetup]
    {P Z Q M S R D E H C K N routeSep routeCompletion routeWindow routeReg routeDyadic
      routeReal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory P ∧ UnaryHistory Z ∧ UnaryHistory Q ∧ UnaryHistory M ∧
      UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory N ∧
          Cont P Z routeSep ∧ Cont routeSep Q routeCompletion ∧
            Cont routeCompletion M routeWindow ∧ Cont routeWindow S routeReg ∧
              Cont routeReg R routeDyadic ∧ Cont routeDyadic D routeReal ∧
                Cont routeReal E C ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg →
      UnaryHistory routeSep ∧ UnaryHistory routeCompletion ∧ UnaryHistory routeWindow ∧
        UnaryHistory routeReg ∧ UnaryHistory routeDyadic ∧ UnaryHistory routeReal ∧
          Cont P Z routeSep ∧ Cont routeSep Q routeCompletion ∧
            Cont routeCompletion M routeWindow ∧ Cont routeWindow S routeReg ∧
              Cont routeReg R routeDyadic ∧ Cont routeDyadic D routeReal ∧
                Cont routeReal E C ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨pUnary, zUnary, qUnary, mUnary, sUnary, rUnary, dUnary, eUnary,
    _hUnary, _cUnary, _kUnary, _nUnary, sepRoute, completionRoute, windowRoute, regRoute,
      dyadicRoute, realRoute, endpointRoute, kPkg, nPkg⟩ := carrier
  have sepUnary : UnaryHistory routeSep :=
    unary_cont_closed pUnary zUnary sepRoute
  have completionUnary : UnaryHistory routeCompletion :=
    unary_cont_closed sepUnary qUnary completionRoute
  have windowUnary : UnaryHistory routeWindow :=
    unary_cont_closed completionUnary mUnary windowRoute
  have regUnary : UnaryHistory routeReg :=
    unary_cont_closed windowUnary sUnary regRoute
  have dyadicUnary : UnaryHistory routeDyadic :=
    unary_cont_closed regUnary rUnary dyadicRoute
  have realUnary : UnaryHistory routeReal :=
    unary_cont_closed dyadicUnary dUnary realRoute
  exact
    ⟨sepUnary, completionUnary, windowUnary, regUnary, dyadicUnary, realUnary,
      sepRoute, completionRoute, windowRoute, regRoute, dyadicRoute, realRoute, endpointRoute,
      kPkg, nPkg⟩

end BEDC.Derived.SeparatedPseudometricCompletionUp
