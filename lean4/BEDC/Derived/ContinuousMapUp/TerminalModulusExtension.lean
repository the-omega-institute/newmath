import BEDC.Derived.ContinuousMapUp.CategoryMetricDecomposition
import BEDC.Derived.ContinuousUp.TerminalModulusExtension

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_terminal_modulus_extension
    {source map target modulus cert extra modulus' cert' distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      ContinuousModulusWitness cert extra cert' ->
        Cont modulus extra modulus' ->
          ContinuousMapCarrier source map target modulus' cert' distance := by
  intro carrier terminalWitness modulusRel
  exact
    And.intro
      (ContinuousFunctionCarrier_terminal_modulus_extension carrier.left terminalWitness
        modulusRel)
      carrier.right

theorem ContinuousMapCarrier_category_metric_terminal_extension_bridge
    {source map target modulus cert extra modulus' cert' distance : BHist} :
    CategoryHomCarrier source target map ->
      ContinuousModulusWitness target modulus cert ->
        MetricDistanceWitness source target distance ->
          ContinuousModulusWitness cert extra cert' ->
            Cont modulus extra modulus' ->
              ContinuousMapCarrier source map target modulus' cert' distance := by
  intro homCarrier modulusWitness distanceWitness terminalWitness modulusRel
  have baseCarrier : ContinuousMapCarrier source map target modulus cert distance :=
    ContinuousMapCarrier_category_metric_decomposition.mpr
      (And.intro homCarrier
        (And.intro modulusWitness
            (And.intro distanceWitness
              (And.intro homCarrier.right.right.right
              (And.intro modulusWitness.right.right.right distanceWitness.right.right.right)))))
  exact ContinuousMapCarrier_terminal_modulus_extension baseCarrier terminalWitness modulusRel

end BEDC.Derived.ContinuousMapUp
