import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.SimplicialComplexUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

theorem SimplicialComplexFace_chain_closure (simplices : ProbeBundle BHist)
    {Simplex : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed : forall {s : BHist}, Simplex s -> InBundle s simplices)
    (faceClosed :
      forall {tau sigma : BHist}, Simplex sigma -> Face tau sigma -> Simplex tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    {rho tau sigma : BHist} :
    Simplex sigma -> Face tau sigma -> Face rho tau ->
      Simplex tau ∧ Simplex rho ∧ Face rho sigma ∧
        InBundle tau simplices ∧ InBundle rho simplices := by
  intro simplexSigma faceTauSigma faceRhoTau
  have simplexTau : Simplex tau :=
    faceClosed simplexSigma faceTauSigma
  have simplexRho : Simplex rho :=
    faceClosed simplexTau faceRhoTau
  have faceRhoSigma : Face rho sigma :=
    faceTrans faceRhoTau faceTauSigma
  have tauListed : InBundle tau simplices :=
    listed simplexTau
  have rhoListed : InBundle rho simplices :=
    listed simplexRho
  exact And.intro simplexTau
    (And.intro simplexRho
      (And.intro faceRhoSigma (And.intro tauListed rhoListed)))

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

theorem SimplicialComplexFace_chain_dimension_monotonicity (simplices : ProbeBundle BHist)
    {Simplex : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed : forall {s : BHist}, Simplex s -> InBundle s simplices)
    (faceClosed :
      forall {tau sigma : BHist}, Simplex sigma -> Face tau sigma -> Simplex tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    (dim : BHist -> Nat)
    (dimMono :
      forall {alpha beta : BHist}, Simplex alpha -> Simplex beta -> Face alpha beta ->
        dim alpha <= dim beta)
    {rho tau sigma : BHist} :
    Simplex sigma -> Face rho tau -> Face tau sigma ->
      dim rho <= dim tau ∧ dim tau <= dim sigma ∧ dim rho <= dim sigma := by
  intro simplexSigma faceRhoTau faceTauSigma
  have closure :=
    SimplicialComplexFace_chain_closure simplices listed faceClosed faceTrans
      simplexSigma faceTauSigma faceRhoTau
  have simplexTau : Simplex tau := closure.left
  have simplexRho : Simplex rho := closure.right.left
  have faceRhoSigma : Face rho sigma := closure.right.right.left
  exact
    And.intro (dimMono simplexRho simplexTau faceRhoTau)
      (And.intro (dimMono simplexTau simplexSigma faceTauSigma)
        (dimMono simplexRho simplexSigma faceRhoSigma))

end BEDC.Derived.SimplicialComplexUp
