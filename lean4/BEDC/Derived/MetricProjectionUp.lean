import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricProjectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricProjectionCarrier [AskSetup] [PackageSetup]
    (H C D I W E T R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory D ∧ UnaryHistory I ∧
    UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory T ∧ UnaryHistory R ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont I W E ∧ Cont D I R ∧
        PkgSig bundle P pkg

theorem MetricProjectionCarrier_closest_point_nonescape [AskSetup] [PackageSetup]
    {H C D I W E T R P N endpoint : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    MetricProjectionCarrier H C D I W E T R P N bundle pkg ->
      Cont I W endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory I ∧ UnaryHistory W ∧
            UnaryHistory E ∧ UnaryHistory endpoint ∧ Cont I W endpoint ∧
              PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRoute endpointPkg
  obtain ⟨HUnary, CUnary, _DUnary, IUnary, WUnary, EUnary, _TUnary, _RUnary,
    _PUnary, _NUnary, _locatedWindow, _distanceReplay, pkgSig⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed IUnary WUnary endpointRoute
  exact
    ⟨HUnary, CUnary, IUnary, WUnary, EUnary, endpointUnary, endpointRoute, pkgSig,
      endpointPkg⟩

end BEDC.Derived.MetricProjectionUp
