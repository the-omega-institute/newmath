import BEDC.Derived.BaireUltrametricUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.BaireUltrametricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem BaireUltrametricCarrier_cylinder_refinement
    [AskSetup] [PackageSetup]
    {B M V S H C P N B' M' V' S' H' C' P' N' windowRefine metricRead
      ultrametricRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame B B' ->
      Cont S S' windowRefine ->
        Cont M V metricRead ->
          Cont windowRefine metricRead ultrametricRead ->
            Cont ultrametricRead N' consumer ->
              PkgSig bundle consumer pkg ->
                baireUltrametricFromEventFlow
                    (baireUltrametricToEventFlow
                      (BaireUltrametricUp.mk B' M' V' S' H' C' P' N')) =
                  some (BaireUltrametricUp.mk B' M' V' S' H' C' P' N') ∧
                  hsame B B' ∧
                    Cont S S' windowRefine ∧
                      Cont M V metricRead ∧
                        Cont windowRefine metricRead ultrametricRead ∧
                          Cont ultrametricRead N' consumer ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro prefixSame windowRoute metricRoute ultrametricRoute consumerRoute consumerPkg
  constructor
  · exact
      (BaireUltrametricTasteGate_single_carrier_alignment).right.right.right.right
        (BaireUltrametricUp.mk B' M' V' S' H' C' P' N')
  · exact
      ⟨prefixSame, windowRoute, metricRoute, ultrametricRoute, consumerRoute,
        consumerPkg⟩

end BEDC.Derived.BaireUltrametricUp
