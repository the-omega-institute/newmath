import BEDC.Derived.InnerProductUp

namespace BEDC.Derived.InnerProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

theorem InnerProductSingleton_public_export_surface {x y : BHist} :
    VecSpaceSingletonCarrier x ->
      VecSpaceSingletonCarrier y ->
        InnerProductSingletonOrthogonal BHist.Empty x ∧
          InnerProductSingletonOrthogonal y BHist.Empty ∧
            InnerProductSingletonOrthogonal x y ∧
              InnerProductSingletonOrthogonal y x ∧
                RealConstantHistoryClassifier (InnerProductSingletonForm x y)
                  (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                  SemanticNameCert VecSpaceSingletonCarrier
                    (fun h : BHist => InnerProductSingletonOrthogonal h BHist.Empty)
                    (fun h : BHist =>
                      RealConstantHistoryClassifier (InnerProductSingletonForm h h)
                        (BHist.e1 (BHist.e1 BHist.Empty)))
                    VecSpaceSingletonClassifier := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert
  intro carrierX carrierY
  have zeroLeft := InnerProductSingletonOrthogonal_zero_left (y := x) carrierX
  have zeroRight := InnerProductSingletonOrthogonal_zero_right (x := y) carrierY
  have exposure := InnerProductRoot_vecspace_scalar_exposure carrierX carrierY
  have orthogonalXY : InnerProductSingletonOrthogonal x y :=
    And.intro exposure.left (And.intro exposure.right.left exposure.right.right)
  have orthogonalYX : InnerProductSingletonOrthogonal y x :=
    (InnerProductSingletonOrthogonal_symm_package orthogonalXY).left
  exact
    ⟨zeroLeft.left, zeroRight.left, orthogonalXY, orthogonalYX, exposure.right.right,
      InnerProductSingleton_semanticNameCert⟩

end BEDC.Derived.InnerProductUp
