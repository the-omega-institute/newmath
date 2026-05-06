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

end BEDC.Derived.SimplicialComplexUp
