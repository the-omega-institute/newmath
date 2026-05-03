import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_empty_composite_factors {a b c f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g BHist.Empty ->
      hsame f BHist.Empty /\ hsame g BHist.Empty /\ hsame a b /\ hsame b c := by
  intro left right comp
  have emptyFactors := cont_empty_result_inversion comp
  have leftEmptyCarrier : CategoryHomCarrier a b BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) emptyFactors.left left
  have rightEmptyCarrier : CategoryHomCarrier b c BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) emptyFactors.right right
  have leftEndpoint := Iff.mp CategoryHomCarrier_empty_identity_iff leftEmptyCarrier
  have rightEndpoint := Iff.mp CategoryHomCarrier_empty_identity_iff rightEmptyCarrier
  exact And.intro emptyFactors.left
    (And.intro emptyFactors.right
      (And.intro leftEndpoint.right.right rightEndpoint.right.right))

theorem CategoryHomCarrier_empty_composite_iff {a b c f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      (Cont f g BHist.Empty <->
        hsame f BHist.Empty /\ hsame g BHist.Empty /\ hsame a b /\ hsame b c) := by
  intro left right
  constructor
  · intro comp
    exact CategoryHomCarrier_empty_composite_factors left right comp
  · intro emptyData
    cases emptyData.left
    cases emptyData.right.left
    rfl

theorem CategoryHomCarrier_e1_endpoint_empty_composite_iff {a b c f g : BHist} :
    CategoryHomCarrier (BHist.e1 a) b f -> CategoryHomCarrier b (BHist.e1 c) g ->
      (Cont f g BHist.Empty <->
        hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame a c) := by
  intro left right
  constructor
  · intro comp
    have emptyData := (CategoryHomCarrier_empty_composite_iff left right).mp comp
    have sameEndpoints : hsame (BHist.e1 a) (BHist.e1 c) :=
      hsame_trans emptyData.right.right.left emptyData.right.right.right
    exact And.intro emptyData.left
      (And.intro emptyData.right.left (hsame_e1_iff.mp sameEndpoints))
  · intro emptyData
    cases emptyData.left
    cases emptyData.right.left
    rfl

theorem CategoryHomCarrier_empty_composite_identity_factors_iff {a b c f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      (Cont f g BHist.Empty <->
        CategoryHomCarrier a b BHist.Empty /\ CategoryHomCarrier b c BHist.Empty) := by
  intro left right
  constructor
  · intro comp
    have emptyFactors := cont_empty_result_inversion comp
    constructor
    · exact CategoryHomCarrier_hsame_transport
        (hsame_refl a) (hsame_refl b) emptyFactors.left left
    · exact CategoryHomCarrier_hsame_transport
        (hsame_refl b) (hsame_refl c) emptyFactors.right right
  · intro emptyCarriers
    have sameLeft : hsame f BHist.Empty :=
      CategoryHomCarrier_morphism_deterministic left emptyCarriers.left
    have sameRight : hsame g BHist.Empty :=
      CategoryHomCarrier_morphism_deterministic right emptyCarriers.right
    cases sameLeft
    cases sameRight
    rfl

theorem CategoryHomCarrier_empty_composite_identity_carriers {a b c f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g BHist.Empty ->
      CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧
        CategoryHomCarrier c c BHist.Empty := by
  intro left right comp
  have emptyFactors := CategoryHomCarrier_empty_composite_factors left right comp
  have leftEmptyCarrier : CategoryHomCarrier a b BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) emptyFactors.left left
  have rightEmptyCarrier : CategoryHomCarrier b c BHist.Empty :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c)
      emptyFactors.right.left right
  have leftEndpoint := Iff.mp CategoryHomCarrier_empty_identity_iff leftEmptyCarrier
  have rightEndpoint := Iff.mp CategoryHomCarrier_empty_identity_iff rightEmptyCarrier
  exact And.intro
    (Iff.mpr CategoryHomCarrier_empty_identity_iff
      (And.intro leftEndpoint.left (And.intro leftEndpoint.left (hsame_refl a))))
    (And.intro
      (Iff.mpr CategoryHomCarrier_empty_identity_iff
        (And.intro leftEndpoint.right.left
          (And.intro leftEndpoint.right.left (hsame_refl b))))
      (Iff.mpr CategoryHomCarrier_empty_identity_iff
        (And.intro rightEndpoint.right.left
          (And.intro rightEndpoint.right.left (hsame_refl c)))))

theorem CategoryHomCarrier_comp_result_empty_iff {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty <->
        hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame a b ∧ hsame b c) := by
  intro left right comp
  constructor
  · intro resultEmpty
    have emptyComp : Cont f g BHist.Empty :=
      cont_result_hsame_transport comp resultEmpty
    exact CategoryHomCarrier_empty_composite_factors left right emptyComp
  · intro emptyData
    have emptyComp : Cont f g BHist.Empty :=
      Iff.mpr (CategoryHomCarrier_empty_composite_iff left right) emptyData
    exact cont_deterministic comp emptyComp

theorem CategoryHomCarrier_comp_result_empty_identity_carriers {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      hsame fg BHist.Empty ->
        CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧
          CategoryHomCarrier c c BHist.Empty := by
  intro left right comp resultEmpty
  have emptyComp : Cont f g BHist.Empty :=
    cont_result_hsame_transport comp resultEmpty
  exact CategoryHomCarrier_empty_composite_identity_carriers left right emptyComp

theorem CategoryHomCarrier_empty_target_comp_boundary_inversion {a b f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b BHist.Empty g -> Cont f g fg ->
      hsame a BHist.Empty ∧ hsame b BHist.Empty ∧ hsame f BHist.Empty ∧
        hsame g BHist.Empty ∧ hsame fg BHist.Empty := by
  intro left right comp
  have rightParts := CategoryHomCarrier_empty_target_iff.mp right
  have leftAsEmptyTarget : CategoryHomCarrier a BHist.Empty f := by
    cases rightParts.left
    exact left
  have leftParts := CategoryHomCarrier_empty_target_iff.mp leftAsEmptyTarget
  have compositeEmpty : hsame fg BHist.Empty := by
    cases leftParts.right
    cases rightParts.right
    cases comp
    rfl
  exact And.intro leftParts.left
    (And.intro rightParts.left
      (And.intro leftParts.right (And.intro rightParts.right compositeEmpty)))

end BEDC.Derived.CategoryUp
