import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_comp_modulus_chain_closed
    {source middle target f g fg modF modG modFG cert certF certG : BHist} :
    ContinuousFunctionCarrier source f middle modF certF ->
      ContinuousFunctionCarrier middle g target modG certG -> Cont f g fg ->
        ContinuousModulusChain target modF modG cert -> Cont modF modG modFG ->
          ContinuousFunctionCarrier source fg target modFG cert := by
  intro first second fgRel chain modRel
  have certWitness : ContinuousModulusWitness target modFG cert :=
    ContinuousModulusChain_composite_closed chain modRel
  exact ContinuousFunctionCarrier_comp_closed first second fgRel modRel certWitness.right.right.right

end BEDC.Derived.ContinuousUp
