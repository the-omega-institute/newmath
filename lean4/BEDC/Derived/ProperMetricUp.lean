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
      UnaryHistory N ∧ Cont X B K ∧ Cont K L T ∧ Cont T H C ∧ PkgSig bundle Q pkg

theorem ProperMetricCarrier_closed_ball_compactness [AskSetup] [PackageSetup]
    {X B K L T H C Q N compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K compactRead ->
        UnaryHistory X ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory compactRead ∧
          Cont X B K ∧ Cont B K compactRead ∧ PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier compactRoute
  obtain ⟨XUnary, BUnary, KUnary, _LUnary, _TUnary, _HUnary, _CUnary, _QUnary,
    _NUnary, metricBallRoute, _locatedRoute, _handoffRoute, pkgSig⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed BUnary KUnary compactRoute
  exact ⟨XUnary, BUnary, KUnary, compactReadUnary, metricBallRoute, compactRoute, pkgSig⟩

end BEDC.Derived.ProperMetricUp
