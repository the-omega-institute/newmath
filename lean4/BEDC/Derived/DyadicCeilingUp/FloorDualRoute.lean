import BEDC.Derived.DyadicCeilingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCeilingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCeilingFloorDualRoute [AskSetup] [PackageSetup]
    {x k c pred lower upper M R E H T P N dyadicWindow realWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont pred c dyadicWindow ->
      Cont dyadicWindow E realWindow ->
        UnaryHistory pred ->
          UnaryHistory c ->
            UnaryHistory E ->
              PkgSig bundle P pkg ->
                UnaryHistory dyadicWindow ∧ UnaryHistory realWindow ∧
                  Cont pred c dyadicWindow ∧ Cont dyadicWindow E realWindow ∧
                    PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro dyadicRoute realRoute predUnary cUnary eUnary provenancePkg
  have dyadicUnary : UnaryHistory dyadicWindow :=
    unary_cont_closed predUnary cUnary dyadicRoute
  have realUnary : UnaryHistory realWindow :=
    unary_cont_closed dyadicUnary eUnary realRoute
  exact ⟨dyadicUnary, realUnary, dyadicRoute, realRoute, provenancePkg⟩

end BEDC.Derived.DyadicCeilingUp
