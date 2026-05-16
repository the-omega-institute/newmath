import BEDC.Derived.CategoryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.Derived.CategoryUp

def KernelCategoryCarrier
    (object hom identity composition associativity unit provenance name : BHist) : Prop :=
  UnaryHistory object ∧
    CategoryHomCarrier object object identity ∧
      Cont identity composition hom ∧
        hsame associativity (append hom composition) ∧
          hsame unit identity ∧
            hsame name (append provenance unit)

theorem KernelCategoryCarrier_identity_continuation
    {object hom identity composition associativity unit provenance name object' identity' : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      hsame object object' →
      hsame identity identity' →
      CategoryHomCarrier object' object' identity' →
      Cont object' identity' object' := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier NameCert
  intro carrier sameObject sameIdentity transportedIdentity
  have baseIdentity : CategoryHomCarrier object object identity := carrier.right.left
  have movedIdentity : CategoryHomCarrier object' object' identity' :=
    CategoryHomCarrier_hsame_transport sameObject sameObject sameIdentity baseIdentity
  have sameDisplayed : hsame identity' BHist.Empty :=
    (CategoryHomCarrier_endomorphism_empty_iff.mp movedIdentity).right
  cases sameDisplayed
  exact cont_right_unit object'

theorem KernelCategoryCarrier_composition_continuation
    {object hom identity composition associativity unit provenance name a b c f g fg : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      CategoryHomCarrier a b f →
        CategoryHomCarrier b c g →
          Cont f g fg →
            CategoryHomCarrier a c fg ∧ hsame associativity (append hom composition) ∧
              hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier
  intro carrier left right comp
  exact
    ⟨CategoryHomCarrier_comp_closed left right comp, carrier.right.right.right.left,
      carrier.right.right.right.right.left, carrier.right.right.right.right.right⟩

theorem KernelCategoryCarrier_certificate_surface
    {object hom identity composition associativity unit provenance name : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row name ∧
              KernelCategoryCarrier object hom identity composition associativity unit
                provenance name)
          (fun row : BHist => hsame row name ∧ Cont identity composition hom)
          (fun row : BHist => hsame row name ∧ hsame unit identity)
          hsame ∧
        UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
          Cont identity composition hom ∧ hsame associativity (append hom composition) ∧
            hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert CategoryHomCarrier
  intro carrier
  have carrierPacket :
      KernelCategoryCarrier object hom identity composition associativity unit provenance name :=
    carrier
  obtain ⟨unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame,
    nameSame⟩ := carrier
  have sourceName :
      (fun row : BHist =>
        hsame row name ∧
          KernelCategoryCarrier object hom identity composition associativity unit
            provenance name) name := by
    exact ⟨hsame_refl name, carrierPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row name ∧
              KernelCategoryCarrier object hom identity composition associativity unit
                provenance name)
          (fun row : BHist => hsame row name ∧ Cont identity composition hom)
          (fun row : BHist => hsame row name ∧ hsame unit identity)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro name sourceName
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, source.right.right.right.left⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, source.right.right.right.right.right.left⟩
    }
  exact
    ⟨cert, unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame,
      nameSame⟩

theorem KernelCategoryCarrier_continuation_monad_consumer_exhaustion
    {object hom identity composition associativity unit provenance name unitRead bindRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      UnaryHistory composition ->
        hsame unitRead identity ->
          Cont hom composition bindRead ->
            UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
              Cont identity composition hom ∧ Cont hom composition bindRead ∧
                hsame unitRead identity ∧ hsame associativity (append hom composition) ∧
                  hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame CategoryHomCarrier
  intro carrier compositionUnary unitReadSame bindRoute
  obtain ⟨_objectUnary, identityCarrier, identityCompositionHom, associativitySame,
    unitSame, nameSame⟩ := carrier
  have identityUnary : UnaryHistory identity :=
    identityCarrier.right.right.left
  have homUnary : UnaryHistory hom :=
    unary_cont_closed identityUnary compositionUnary identityCompositionHom
  have unitReadUnary : UnaryHistory unitRead :=
    unary_transport identityUnary (hsame_symm unitReadSame)
  have bindUnary : UnaryHistory bindRead :=
    unary_cont_closed homUnary compositionUnary bindRoute
  exact
    ⟨unitReadUnary, bindUnary, identityCompositionHom, bindRoute, unitReadSame,
      associativitySame, unitSame, nameSame⟩

theorem KernelCategoryCarrier_cont_composition_stability
    {object hom identity composition associativity unit provenance name a b c f g fg fPrime
      gPrime fgPrime : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      CategoryHomCarrier a b f ->
        CategoryHomCarrier b c g ->
          Cont f g fg ->
            hsame f fPrime ->
              hsame g gPrime ->
                Cont fPrime gPrime fgPrime ->
                  CategoryHomCarrier a c fg ∧ hsame fg fgPrime ∧
                    CategoryHomCarrier a c fgPrime := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier
  intro _carrier left right comp sameF sameG compPrime
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have sameComposite : hsame fg fgPrime :=
    cont_respects_hsame sameF sameG comp compPrime
  have compositePrime : CategoryHomCarrier a c fgPrime :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl c) sameComposite composite
  exact ⟨composite, sameComposite, compositePrime⟩

end BEDC.Derived.KernelCategoryUp
