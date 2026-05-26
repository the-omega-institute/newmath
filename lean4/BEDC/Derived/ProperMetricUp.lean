import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProperMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ProperMetricCarrier [AskSetup] [PackageSetup]
    (X B K L T H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory L ∧
    UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧
      UnaryHistory N ∧ Cont X B K ∧ Cont K L T ∧ Cont T H C ∧
        PkgSig bundle Q pkg

theorem ProperMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X B K L T H C Q N closedCompact locatedComplete : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K closedCompact ->
        Cont K L locatedComplete ->
          PkgSig bundle closedCompact pkg ->
            PkgSig bundle locatedComplete pkg ->
              UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧
                  UnaryHistory N ∧ UnaryHistory closedCompact ∧
                    UnaryHistory locatedComplete ∧ Cont X B K ∧ Cont K L T ∧
                      Cont T H C ∧ Cont B K closedCompact ∧
                        Cont K L locatedComplete ∧ PkgSig bundle Q pkg ∧
                          PkgSig bundle closedCompact pkg ∧
                            PkgSig bundle locatedComplete pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier closedRoute locatedRoute closedPkg locatedPkg
  obtain ⟨XUnary, BUnary, KUnary, LUnary, TUnary, HUnary, CUnary, QUnary, NUnary,
    metricClosedRoute, compactLocatedRoute, handoffRoute, properPkg⟩ := carrier
  have closedUnary : UnaryHistory closedCompact :=
    unary_cont_closed BUnary KUnary closedRoute
  have locatedUnary : UnaryHistory locatedComplete :=
    unary_cont_closed KUnary LUnary locatedRoute
  exact
    ⟨XUnary, BUnary, KUnary, LUnary, TUnary, HUnary, CUnary, QUnary, NUnary,
      closedUnary, locatedUnary, metricClosedRoute, compactLocatedRoute, handoffRoute,
      closedRoute, locatedRoute, properPkg, closedPkg, locatedPkg⟩

end BEDC.Derived.ProperMetricUp
