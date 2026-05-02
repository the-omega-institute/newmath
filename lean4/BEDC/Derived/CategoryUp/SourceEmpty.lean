import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_empty_morphism_iff {a target : BHist} :
    CategoryHomCarrier (BHist.e1 a) target BHist.Empty ↔
      target = BHist.e1 a ∧ UnaryHistory a := by
  constructor
  · intro homCarrier
    have identityData :=
      (CategoryHomCarrier_empty_identity_iff
        (a := BHist.e1 a) (b := target)).mp homCarrier
    cases identityData with
    | intro sourceCarrier rest =>
        cases rest with
        | intro _targetCarrier sameTarget =>
            cases sameTarget
            exact And.intro rfl (unary_e1_inversion sourceCarrier)
  · intro data
    cases data with
    | intro targetEq sourceCarrier =>
        cases targetEq
        exact CategoryHomCarrier_empty_identity (unary_e1_closed sourceCarrier)

theorem CategoryHomCarrier_empty_source_morphism_target_deterministic {b c f g : BHist} :
    CategoryHomCarrier BHist.Empty b f -> CategoryHomCarrier BHist.Empty c g ->
      hsame f g -> hsame b c := by
  intro left right sameMorphism
  have movedRight : CategoryHomCarrier BHist.Empty c f :=
    CategoryHomCarrier_hsame_transport (hsame_refl BHist.Empty) (hsame_refl c)
      (hsame_symm sameMorphism) right
  exact CategoryHomCarrier_target_deterministic left movedRight

end BEDC.Derived.CategoryUp
