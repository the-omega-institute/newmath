import BEDC.Derived.ContractionMappingUp.OrbitReadiness

namespace BEDC.Derived.ContractionMappingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContractionMappingCarrier_scoped_dependency_surface [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay tailReplay
      metricRead graphRead modulusRead completeRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay tailReplay →
        Cont X d metricRead →
          Cont T G graphRead →
            Cont lambda M modulusRead →
              Cont metricRead graphRead completeRead →
                Cont completeRead P sealRead →
                  PkgSig bundle sealRead pkg →
                    UnaryHistory X ∧ UnaryHistory d ∧ UnaryHistory T ∧ UnaryHistory G ∧
                      UnaryHistory lambda ∧ UnaryHistory M ∧ UnaryHistory I ∧
                        UnaryHistory x0 ∧ UnaryHistory iterates ∧ UnaryHistory boundPower ∧
                          UnaryHistory tolerance ∧ UnaryHistory metricRead ∧
                            UnaryHistory graphRead ∧ UnaryHistory modulusRead ∧
                              UnaryHistory completeRead ∧ UnaryHistory sealRead ∧
                                Cont X d metricRead ∧ Cont T G graphRead ∧
                                  Cont lambda M modulusRead ∧
                                    Cont metricRead graphRead completeRead ∧
                                      Cont completeRead P sealRead ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier orbit metricRoute graphRoute modulusRoute completeRoute sealRoute sealPkg
  obtain ⟨XUnary, dUnary, TUnary, GUnary, lambdaUnary, MUnary, IUnary, _HUnary,
    _CUnary, PUnary, _NUnary, provenancePkg⟩ := carrier
  obtain ⟨x0Unary, iteratesUnary, boundPowerUnary, toleranceUnary, _adjacentRoute,
    _tailRoute⟩ := orbit
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed XUnary dUnary metricRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed TUnary GUnary graphRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed lambdaUnary MUnary modulusRoute
  have completeReadUnary : UnaryHistory completeRead :=
    unary_cont_closed metricReadUnary graphReadUnary completeRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed completeReadUnary PUnary sealRoute
  exact
    ⟨XUnary, dUnary, TUnary, GUnary, lambdaUnary, MUnary, IUnary, x0Unary,
      iteratesUnary, boundPowerUnary, toleranceUnary, metricReadUnary, graphReadUnary,
      modulusReadUnary, completeReadUnary, sealReadUnary, metricRoute, graphRoute,
      modulusRoute, completeRoute, sealRoute, provenancePkg, sealPkg⟩

theorem ContractionMappingCarrier_completion_readiness_scope [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay tailReplay
      completeRead tailRead readinessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay tailReplay →
        Cont I M completeRead →
          Cont completeRead C tailRead →
            Cont tailRead P readinessRead →
              PkgSig bundle readinessRead pkg →
                UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory completeRead ∧
                  UnaryHistory tailRead ∧ UnaryHistory readinessRead ∧
                    Cont I M completeRead ∧ Cont completeRead C tailRead ∧
                      Cont tailRead P readinessRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle readinessRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier _orbit completeRoute tailRoute readinessRoute readinessPkg
  obtain ⟨_XUnary, _dUnary, _TUnary, _GUnary, _lambdaUnary, MUnary, IUnary, _HUnary,
    CUnary, PUnary, _NUnary, provenancePkg⟩ := carrier
  have completeReadUnary : UnaryHistory completeRead :=
    unary_cont_closed IUnary MUnary completeRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed completeReadUnary CUnary tailRoute
  have readinessReadUnary : UnaryHistory readinessRead :=
    unary_cont_closed tailReadUnary PUnary readinessRoute
  exact
    ⟨IUnary, MUnary, completeReadUnary, tailReadUnary, readinessReadUnary,
      completeRoute, tailRoute, readinessRoute, provenancePkg, readinessPkg⟩

end BEDC.Derived.ContractionMappingUp
