import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.SimplicialComplexUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

structure SimplicialComplexFiniteFaceCarrier : Type where
  support : ProbeBundle BHist
  Simplex : BHist -> Prop
  Face : BHist -> BHist -> Prop
  listed : forall {s : BHist}, Simplex s -> InBundle s support
  face_closed : forall {tau sigma : BHist}, Simplex sigma -> Face tau sigma -> Simplex tau
  face_trans : forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma

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

theorem SimplicialComplexFace_dimension_chain_monotonicity (simplices : ProbeBundle BHist)
    {Simplex : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed : forall {s : BHist}, Simplex s -> InBundle s simplices)
    (faceClosed :
      forall {tau sigma : BHist}, Simplex sigma -> Face tau sigma -> Simplex tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    (dim : BHist -> Nat)
    (dimMono :
      forall {alpha beta : BHist},
        Simplex alpha -> Simplex beta -> Face alpha beta -> dim alpha <= dim beta)
    {rho tau sigma : BHist} :
    Simplex sigma -> Face rho tau -> Face tau sigma ->
      dim rho <= dim tau ∧ dim tau <= dim sigma ∧ dim rho <= dim sigma := by
  intro simplexSigma faceRhoTau faceTauSigma
  have chain :=
    SimplicialComplexFace_chain_closure simplices listed faceClosed faceTrans
      simplexSigma faceTauSigma faceRhoTau
  have simplexTau : Simplex tau := chain.left
  have simplexRho : Simplex rho := chain.right.left
  have faceRhoSigma : Face rho sigma := chain.right.right.left
  have dimRhoTau : dim rho <= dim tau :=
    dimMono simplexRho simplexTau faceRhoTau
  have dimTauSigma : dim tau <= dim sigma :=
    dimMono simplexTau simplexSigma faceTauSigma
  have dimRhoSigma : dim rho <= dim sigma :=
    dimMono simplexRho simplexSigma faceRhoSigma
  exact And.intro dimRhoTau (And.intro dimTauSigma dimRhoSigma)

theorem SimplicialComplexIntersection_face_chain_closure (simplices : ProbeBundle BHist)
    {SimplexK SimplexL : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed :
      forall {s : BHist}, SimplexK s ∧ SimplexL s -> InBundle s simplices)
    (faceClosedK :
      forall {tau sigma : BHist}, SimplexK sigma -> Face tau sigma -> SimplexK tau)
    (faceClosedL :
      forall {tau sigma : BHist}, SimplexL sigma -> Face tau sigma -> SimplexL tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    {rho tau sigma : BHist} :
    SimplexK sigma ∧ SimplexL sigma -> Face tau sigma -> Face rho tau ->
      (SimplexK tau ∧ SimplexL tau) ∧
        (SimplexK rho ∧ SimplexL rho) ∧ Face rho sigma ∧
          InBundle tau simplices ∧ InBundle rho simplices := by
  intro simplexSigma faceTauSigma faceRhoTau
  have simplexTauK : SimplexK tau :=
    faceClosedK simplexSigma.left faceTauSigma
  have simplexTauL : SimplexL tau :=
    faceClosedL simplexSigma.right faceTauSigma
  have simplexTau : SimplexK tau ∧ SimplexL tau :=
    And.intro simplexTauK simplexTauL
  have simplexRhoK : SimplexK rho :=
    faceClosedK simplexTauK faceRhoTau
  have simplexRhoL : SimplexL rho :=
    faceClosedL simplexTauL faceRhoTau
  have simplexRho : SimplexK rho ∧ SimplexL rho :=
    And.intro simplexRhoK simplexRhoL
  have faceRhoSigma : Face rho sigma :=
    faceTrans faceRhoTau faceTauSigma
  have tauListed : InBundle tau simplices :=
    listed simplexTau
  have rhoListed : InBundle rho simplices :=
    listed simplexRho
  exact And.intro simplexTau
    (And.intro simplexRho
      (And.intro faceRhoSigma (And.intro tauListed rhoListed)))

theorem SimplicialComplexIntersection_face_dimension_grading (simplices : ProbeBundle BHist)
    {SimplexK SimplexL : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed :
      forall {s : BHist}, SimplexK s ∧ SimplexL s -> InBundle s simplices)
    (faceClosedK :
      forall {tau sigma : BHist}, SimplexK sigma -> Face tau sigma -> SimplexK tau)
    (faceClosedL :
      forall {tau sigma : BHist}, SimplexL sigma -> Face tau sigma -> SimplexL tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    (dim : BHist -> Nat)
    (dimMonoK :
      forall {alpha beta : BHist},
        SimplexK alpha -> SimplexK beta -> Face alpha beta -> dim alpha <= dim beta)
    {rho tau sigma : BHist} :
    SimplexK sigma ∧ SimplexL sigma -> Face tau sigma -> Face rho tau ->
      dim rho <= dim tau ∧ dim tau <= dim sigma ∧ dim rho <= dim sigma := by
  intro simplexSigma faceTauSigma faceRhoTau
  have chain :=
    SimplicialComplexIntersection_face_chain_closure simplices listed faceClosedK
      faceClosedL faceTrans simplexSigma faceTauSigma faceRhoTau
  have simplexTauK : SimplexK tau := chain.left.left
  have simplexRhoK : SimplexK rho := chain.right.left.left
  have faceRhoSigma : Face rho sigma := chain.right.right.left
  have dimRhoTau : dim rho <= dim tau :=
    dimMonoK simplexRhoK simplexTauK faceRhoTau
  have dimTauSigma : dim tau <= dim sigma :=
    dimMonoK simplexTauK simplexSigma.left faceTauSigma
  have dimRhoSigma : dim rho <= dim sigma :=
    dimMonoK simplexRhoK simplexSigma.left faceRhoSigma
  exact And.intro dimRhoTau (And.intro dimTauSigma dimRhoSigma)

theorem SimplicialComplexUnion_face_chain_closure (simplices : ProbeBundle BHist)
    {SimplexK SimplexL : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed : forall {s : BHist}, SimplexK s ∨ SimplexL s -> InBundle s simplices)
    (faceClosedK :
      forall {tau sigma : BHist}, SimplexK sigma -> Face tau sigma -> SimplexK tau)
    (faceClosedL :
      forall {tau sigma : BHist}, SimplexL sigma -> Face tau sigma -> SimplexL tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    {rho tau sigma : BHist} :
    SimplexK sigma ∨ SimplexL sigma -> Face tau sigma -> Face rho tau ->
      (SimplexK tau ∨ SimplexL tau) ∧ (SimplexK rho ∨ SimplexL rho) ∧
        Face rho sigma ∧ InBundle tau simplices ∧ InBundle rho simplices := by
  intro simplexSigma faceTauSigma faceRhoTau
  have simplexTau : SimplexK tau ∨ SimplexL tau := by
    cases simplexSigma with
    | inl simplexSigmaK =>
        exact Or.inl (faceClosedK simplexSigmaK faceTauSigma)
    | inr simplexSigmaL =>
        exact Or.inr (faceClosedL simplexSigmaL faceTauSigma)
  have simplexRho : SimplexK rho ∨ SimplexL rho := by
    cases simplexTau with
    | inl simplexTauK =>
        exact Or.inl (faceClosedK simplexTauK faceRhoTau)
    | inr simplexTauL =>
        exact Or.inr (faceClosedL simplexTauL faceRhoTau)
  have faceRhoSigma : Face rho sigma :=
    faceTrans faceRhoTau faceTauSigma
  have tauListed : InBundle tau simplices :=
    listed simplexTau
  have rhoListed : InBundle rho simplices :=
    listed simplexRho
  exact And.intro simplexTau
    (And.intro simplexRho
      (And.intro faceRhoSigma (And.intro tauListed rhoListed)))

theorem SimplicialComplexUnion_face_dimension_grading (simplices : ProbeBundle BHist)
    {SimplexK SimplexL : BHist -> Prop} {Face : BHist -> BHist -> Prop}
    (listed : forall {s : BHist}, SimplexK s ∨ SimplexL s -> InBundle s simplices)
    (faceClosedK :
      forall {tau sigma : BHist}, SimplexK sigma -> Face tau sigma -> SimplexK tau)
    (faceClosedL :
      forall {tau sigma : BHist}, SimplexL sigma -> Face tau sigma -> SimplexL tau)
    (faceTrans :
      forall {rho tau sigma : BHist}, Face rho tau -> Face tau sigma -> Face rho sigma)
    (dim : BHist -> Nat)
    (dimMonoK :
      forall {alpha beta : BHist},
        SimplexK alpha -> SimplexK beta -> Face alpha beta -> dim alpha <= dim beta)
    (dimMonoL :
      forall {alpha beta : BHist},
        SimplexL alpha -> SimplexL beta -> Face alpha beta -> dim alpha <= dim beta)
    {rho tau sigma : BHist} :
    SimplexK sigma ∨ SimplexL sigma -> Face tau sigma -> Face rho tau ->
      dim rho <= dim tau ∧ dim tau <= dim sigma ∧ dim rho <= dim sigma := by
  intro simplexSigma faceTauSigma faceRhoTau
  have faceRhoSigma : Face rho sigma :=
    faceTrans faceRhoTau faceTauSigma
  cases simplexSigma with
  | inl simplexSigmaK =>
      have simplexTauK : SimplexK tau :=
        faceClosedK simplexSigmaK faceTauSigma
      have simplexRhoK : SimplexK rho :=
        faceClosedK simplexTauK faceRhoTau
      have dimRhoTau : dim rho <= dim tau :=
        dimMonoK simplexRhoK simplexTauK faceRhoTau
      have dimTauSigma : dim tau <= dim sigma :=
        dimMonoK simplexTauK simplexSigmaK faceTauSigma
      have dimRhoSigma : dim rho <= dim sigma :=
        dimMonoK simplexRhoK simplexSigmaK faceRhoSigma
      exact And.intro dimRhoTau (And.intro dimTauSigma dimRhoSigma)
  | inr simplexSigmaL =>
      have simplexTauL : SimplexL tau :=
        faceClosedL simplexSigmaL faceTauSigma
      have simplexRhoL : SimplexL rho :=
        faceClosedL simplexTauL faceRhoTau
      have dimRhoTau : dim rho <= dim tau :=
        dimMonoL simplexRhoL simplexTauL faceRhoTau
      have dimTauSigma : dim tau <= dim sigma :=
        dimMonoL simplexTauL simplexSigmaL faceTauSigma
      have dimRhoSigma : dim rho <= dim sigma :=
        dimMonoL simplexRhoL simplexSigmaL faceRhoSigma
      exact And.intro dimRhoTau (And.intro dimTauSigma dimRhoSigma)

end BEDC.Derived.SimplicialComplexUp
