import BEDC.Derived.ContinuousMapUp.TerminalModulusExtension

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapPublic_export_surface
    {source map target modulus cert extra modulus' cert' distance : BHist} :
    CategoryHomCarrier source target map ->
      ContinuousModulusWitness target modulus cert ->
        MetricDistanceWitness source target distance ->
          ContinuousModulusWitness cert extra cert' ->
            Cont modulus extra modulus' ->
              ContinuousMapCarrier source map target modulus' cert' distance ∧
                CategoryHomCarrier source target map ∧
                  MetricDistanceWitness source target distance := by
  intro homCarrier modulusWitness distanceWitness terminalWitness modulusRel
  have carrier : ContinuousMapCarrier source map target modulus' cert' distance :=
    ContinuousMapCarrier_category_metric_terminal_extension_bridge homCarrier modulusWitness
      distanceWitness terminalWitness modulusRel
  exact And.intro carrier (And.intro homCarrier distanceWitness)

end BEDC.Derived.ContinuousMapUp
