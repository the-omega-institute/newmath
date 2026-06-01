import BEDC.Derived.BaireUltrametricUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireUltrametricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireUltrametricCarrier_finite_cylinder_completion_handoff
    [AskSetup] [PackageSetup]
    {B M V S H C P N prefixRead metricRead ultrametricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory S ->
        UnaryHistory M ->
          UnaryHistory V ->
            UnaryHistory N ->
              Cont B S prefixRead ->
                Cont prefixRead M metricRead ->
                  Cont metricRead V ultrametricRead ->
                    Cont ultrametricRead N completionRead ->
                      PkgSig bundle completionRead pkg ->
                        baireUltrametricFromEventFlow
                            (baireUltrametricToEventFlow
                              (BaireUltrametricUp.mk B M V S H C P N)) =
                          some (BaireUltrametricUp.mk B M V S H C P N) ∧
                          UnaryHistory prefixRead ∧
                            UnaryHistory metricRead ∧
                              UnaryHistory ultrametricRead ∧
                                UnaryHistory completionRead ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro unaryB unaryS unaryM unaryV unaryN prefixRoute metricRoute ultrametricRoute
    completionRoute completionPkg
  have roundTrip :
      baireUltrametricFromEventFlow
          (baireUltrametricToEventFlow (BaireUltrametricUp.mk B M V S H C P N)) =
        some (BaireUltrametricUp.mk B M V S H C P N) :=
    (BaireUltrametricTasteGate_single_carrier_alignment).right.right.right.right
      (BaireUltrametricUp.mk B M V S H C P N)
  have unaryPrefix : UnaryHistory prefixRead :=
    unary_cont_closed unaryB unaryS prefixRoute
  have unaryMetric : UnaryHistory metricRead :=
    unary_cont_closed unaryPrefix unaryM metricRoute
  have unaryUltrametric : UnaryHistory ultrametricRead :=
    unary_cont_closed unaryMetric unaryV ultrametricRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unaryUltrametric unaryN completionRoute
  exact
    ⟨roundTrip, unaryPrefix, unaryMetric, unaryUltrametric, unaryCompletion,
      completionPkg⟩

end BEDC.Derived.BaireUltrametricUp
