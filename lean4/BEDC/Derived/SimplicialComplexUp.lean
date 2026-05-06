import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.SimplicialComplexUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def SimplicialFaceCarrier (simplices : ProbeBundle BHist) (Face : BHist -> BHist -> Prop)
    (sigma : BHist) : Prop :=
  InBundle sigma simplices ∧
    forall {tau : BHist}, Face tau sigma -> InBundle tau simplices

theorem SimplicialFaceCarrier_face_chain_closure {simplices : ProbeBundle BHist}
    {Face : BHist -> BHist -> Prop}
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    {rho tau sigma : BHist} :
    SimplicialFaceCarrier simplices Face sigma -> Face tau sigma -> Face rho tau ->
      SimplicialFaceCarrier simplices Face tau ∧
        SimplicialFaceCarrier simplices Face rho ∧ Face rho sigma := by
  intro sigmaCarrier tauFaceSigma rhoFaceTau
  have tauIn : InBundle tau simplices := sigmaCarrier.right tauFaceSigma
  have rhoFaceSigma : Face rho sigma := faceTrans rhoFaceTau tauFaceSigma
  have rhoIn : InBundle rho simplices := sigmaCarrier.right rhoFaceSigma
  have tauCarrier : SimplicialFaceCarrier simplices Face tau := by
    constructor
    · exact tauIn
    · intro nu nuFaceTau
      exact sigmaCarrier.right (faceTrans nuFaceTau tauFaceSigma)
  have rhoCarrier : SimplicialFaceCarrier simplices Face rho := by
    constructor
    · exact rhoIn
    · intro nu nuFaceRho
      exact sigmaCarrier.right (faceTrans nuFaceRho rhoFaceSigma)
  exact And.intro tauCarrier (And.intro rhoCarrier rhoFaceSigma)

end BEDC.Derived.SimplicialComplexUp
