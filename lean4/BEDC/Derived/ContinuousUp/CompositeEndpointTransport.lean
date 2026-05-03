import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousModulusChain_composite_endpoint_hsame_transport
    {source source' first second target target' composite composite' : BHist} :
    hsame source source' -> hsame target target' -> hsame composite composite' ->
      ContinuousModulusChain source first second target -> Cont first second composite ->
        ContinuousModulusWitness source' composite' target' := by
  intro sameSource sameTarget sameComposite chain compositeRel
  cases sameSource
  cases sameTarget
  cases sameComposite
  exact ContinuousModulusChain_composite_closed chain compositeRel

theorem ContinuousFunctionCarrier_comp_endpoint_hsame_transport
    {source source' middle target target' f g fg fg' modF modG modFG modFG' certF certG
      cert cert' : BHist} :
    hsame source source' -> hsame target target' -> hsame fg fg' -> hsame modFG modFG' ->
      hsame cert cert' -> ContinuousFunctionCarrier source f middle modF certF ->
        ContinuousFunctionCarrier middle g target modG certG -> Cont f g fg ->
          Cont modF modG modFG -> Cont target modFG cert ->
            ContinuousFunctionCarrier source' fg' target' modFG' cert' := by
  intro sameSource sameTarget sameMap sameModulus sameCert first second fgRel modRel certRel
  cases sameSource
  cases sameTarget
  cases sameMap
  cases sameModulus
  cases sameCert
  exact ContinuousFunctionCarrier_comp_closed first second fgRel modRel certRel

end BEDC.Derived.ContinuousUp
