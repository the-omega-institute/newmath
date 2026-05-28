import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactnessCompactMetricRoute [AskSetup] [PackageSetup]
    {compactSource sequenceWindow selectorWindow readback realSeal transport routeConsumer
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactSource →
      UnaryHistory sequenceWindow →
        UnaryHistory readback →
          UnaryHistory transport →
            Cont compactSource sequenceWindow selectorWindow →
              Cont selectorWindow readback realSeal →
                Cont realSeal transport routeConsumer →
                  PkgSig bundle compactSource pkg →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle routeConsumer pkg →
                        UnaryHistory selectorWindow ∧
                          UnaryHistory realSeal ∧
                            UnaryHistory routeConsumer ∧
                              Cont compactSource sequenceWindow selectorWindow ∧
                                Cont selectorWindow readback realSeal ∧
                                  Cont realSeal transport routeConsumer ∧
                                    PkgSig bundle compactSource pkg ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle routeConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro compactUnary sequenceUnary readbackUnary transportUnary selectorRoute realSealRoute
    consumerRoute compactPkg provenancePkg consumerPkg
  have selectorUnary : UnaryHistory selectorWindow :=
    unary_cont_closed compactUnary sequenceUnary selectorRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed selectorUnary readbackUnary realSealRoute
  have routeConsumerUnary : UnaryHistory routeConsumer :=
    unary_cont_closed realSealUnary transportUnary consumerRoute
  exact
    ⟨selectorUnary, realSealUnary, routeConsumerUnary, selectorRoute, realSealRoute,
      consumerRoute, compactPkg, provenancePkg, consumerPkg⟩

end BEDC.Derived.SequentialCompactnessUp
