import BEDC.Derived.CategoryUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
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

theorem KernelCategoryCarrier_associativity_scope
    {object hom identity composition associativity unit provenance name a b c d f g h fg gh left
      right lawRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      CategoryHomCarrier a b f →
        CategoryHomCarrier b c g →
          CategoryHomCarrier c d h →
            Cont f g fg →
              Cont g h gh →
                Cont fg h left →
                  Cont f gh right →
                    Cont left right lawRead →
                      CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧
                        UnaryHistory lawRead ∧ Cont left right lawRead ∧
                          hsame associativity (append hom composition) ∧
                            hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CategoryHomCarrier
  intro carrier first second third fgRel ghRel leftRel rightRel lawRel
  have composites :
      CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right :=
    CategoryHomCarrier_comp_assoc_closed first second third fgRel ghRel leftRel rightRel
  have lawUnary : UnaryHistory lawRead :=
    unary_cont_closed composites.left.right.right.left composites.right.left.right.right.left
      lawRel
  exact
    ⟨composites.left, composites.right.left, lawUnary, lawRel,
      carrier.right.right.right.left, carrier.right.right.right.right.right⟩

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

theorem KernelCategoryCarrier_identity_cont_route_exhaustion
    {object hom identity composition associativity unit provenance name identityRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      hsame identityRead identity →
        SemanticNameCert
            (fun row : BHist => hsame row identityRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row identityRead ∧ Cont object identity object)
            (fun row : BHist => hsame row identityRead ∧ hsame name (append provenance unit))
            hsame ∧
          Cont object identity object ∧ hsame identityRead identity ∧
            hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier identitySame
  have carrierPacket :
      KernelCategoryCarrier object hom identity composition associativity unit provenance name :=
    carrier
  obtain ⟨_unaryObject, identityCarrier, _compositionRoute, _associativitySame,
    _unitSame, nameSame⟩ := carrier
  have identityObjectRoute : Cont object identity object := by
    exact KernelCategoryCarrier_identity_continuation carrierPacket (hsame_refl object)
      (hsame_refl identity) identityCarrier
  have unaryIdentity : UnaryHistory identity :=
    identityCarrier.right.right.left
  have unaryIdentityRead : UnaryHistory identityRead :=
    unary_transport unaryIdentity (hsame_symm identitySame)
  have sourceIdentityRead :
      (fun row : BHist => hsame row identityRead ∧ UnaryHistory row) identityRead := by
    exact ⟨hsame_refl identityRead, unaryIdentityRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row identityRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row identityRead ∧ Cont object identity object)
          (fun row : BHist => hsame row identityRead ∧ hsame name (append provenance unit))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro identityRead sourceIdentityRead
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, identityObjectRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, nameSame⟩
    }
  exact ⟨cert, identityObjectRoute, identitySame, nameSame⟩

theorem KernelCategoryCarrier_object_hom_law_separation
    {object hom identity composition associativity unit provenance name lawRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      Cont associativity unit lawRead →
        UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
          Cont identity composition hom ∧ hsame associativity (append hom composition) ∧
            hsame unit identity ∧ hsame name (append provenance unit) ∧
              SemanticNameCert
                (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
                (fun row : BHist =>
                  hsame row lawRead ∧ hsame associativity (append hom composition))
                (fun row : BHist =>
                  hsame row lawRead ∧ hsame unit identity ∧
                    hsame name (append provenance unit))
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert CategoryHomCarrier
  intro carrier lawRoute
  obtain ⟨unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame,
    nameSame⟩ := carrier
  have sourceLaw :
      (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        lawRead := by
    exact ⟨hsame_refl lawRead, lawRoute⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        (fun row : BHist =>
          hsame row lawRead ∧ hsame associativity (append hom composition))
        (fun row : BHist =>
          hsame row lawRead ∧ hsame unit identity ∧ hsame name (append provenance unit))
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lawRead sourceLaw
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
        exact ⟨source.left, associativitySame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, unitSame, nameSame⟩
    }
  exact
    ⟨unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame, nameSame,
      cert⟩

theorem KernelCategoryCarrier_root_transport_nonescape [BEDC.FKernel.Ask.AskSetup]
    [BEDC.FKernel.Package.PackageSetup]
    {object hom identity composition associativity unit provenance name endpoint' hom'
      lawRead : BHist}
    {bundle : BEDC.FKernel.Bundle.ProbeBundle BEDC.FKernel.Ask.ProbeName}
    {pkg : BEDC.FKernel.Package.Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      hsame object endpoint' →
        hsame hom hom' →
          Cont associativity unit lawRead →
            BEDC.FKernel.Package.PkgSig bundle lawRead pkg →
              UnaryHistory object ∧ UnaryHistory endpoint' ∧
                CategoryHomCarrier object object identity ∧ Cont identity composition hom ∧
                  hsame hom hom' ∧ hsame associativity (append hom composition) ∧
                    hsame unit identity ∧ hsame name (append provenance unit) ∧
                      BEDC.FKernel.Package.PkgSig bundle lawRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist =>
                            hsame row lawRead ∧ Cont associativity unit lawRead)
                          (fun row : BHist =>
                            hsame row lawRead ∧ hsame associativity (append hom composition))
                          (fun row : BHist =>
                            hsame row lawRead ∧
                              BEDC.FKernel.Package.PkgSig bundle lawRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert CategoryHomCarrier PkgSig
  intro carrier sameObject sameHom lawRoute lawPkg
  obtain ⟨unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame,
    nameSame⟩ := carrier
  have unaryEndpoint : UnaryHistory endpoint' :=
    unary_transport unaryObject sameObject
  have sourceLaw :
      (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        lawRead := by
    exact ⟨hsame_refl lawRead, lawRoute⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        (fun row : BHist =>
          hsame row lawRead ∧ hsame associativity (append hom composition))
        (fun row : BHist =>
          hsame row lawRead ∧ BEDC.FKernel.Package.PkgSig bundle lawRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lawRead sourceLaw
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
        exact ⟨source.left, associativitySame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, lawPkg⟩
    }
  exact
    ⟨unaryObject, unaryEndpoint, identityCarrier, compositionRoute, sameHom,
      associativitySame, unitSame, nameSame, lawPkg, cert⟩

theorem KernelCategoryCarrier_route_totality [BEDC.FKernel.Ask.AskSetup]
    [BEDC.FKernel.Package.PackageSetup]
    {object hom identity composition associativity unit provenance name routeRead : BHist}
    {bundle : BEDC.FKernel.Bundle.ProbeBundle BEDC.FKernel.Ask.ProbeName}
    {pkg : BEDC.FKernel.Package.Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      UnaryHistory composition ->
        Cont hom composition routeRead ->
          BEDC.FKernel.Package.PkgSig bundle routeRead pkg ->
            UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
              Cont identity composition hom ∧ UnaryHistory routeRead ∧
                Cont hom composition routeRead ∧ hsame associativity (append hom composition) ∧
                  hsame unit identity ∧ hsame name (append provenance unit) ∧
                    BEDC.FKernel.Package.PkgSig bundle routeRead pkg ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row routeRead ∧ Cont hom composition routeRead)
                        (fun row : BHist =>
                          hsame row routeRead ∧
                            BEDC.FKernel.Package.PkgSig bundle routeRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert PkgSig
  intro carrier compositionUnary routeCont routePkg
  obtain ⟨unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame,
    nameSame⟩ := carrier
  have identityUnary : UnaryHistory identity :=
    identityCarrier.right.right.left
  have homUnary : UnaryHistory hom :=
    unary_cont_closed identityUnary compositionUnary compositionRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed homUnary compositionUnary routeCont
  have sourceRoute :
      (fun row : BHist => hsame row routeRead ∧ UnaryHistory row) routeRead := by
    exact ⟨hsame_refl routeRead, routeUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row routeRead ∧ Cont hom composition routeRead)
        (fun row : BHist =>
          hsame row routeRead ∧ BEDC.FKernel.Package.PkgSig bundle routeRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro routeRead sourceRoute
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
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, routeCont⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, routePkg⟩
    }
  exact
    ⟨unaryObject, identityCarrier, compositionRoute, routeUnary, routeCont,
      associativitySame, unitSame, nameSame, routePkg, cert⟩

theorem KernelCategoryCarrier_law_row_exactness [BEDC.FKernel.Ask.AskSetup]
    [BEDC.FKernel.Package.PackageSetup]
    {object hom identity composition associativity unit provenance name lawRead : BHist}
    {bundle : BEDC.FKernel.Bundle.ProbeBundle BEDC.FKernel.Ask.ProbeName}
    {pkg : BEDC.FKernel.Package.Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      Cont associativity unit lawRead ->
        BEDC.FKernel.Package.PkgSig bundle lawRead pkg ->
          UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
            Cont identity composition hom ∧ Cont associativity unit lawRead ∧
              hsame associativity (append hom composition) ∧ hsame unit identity ∧
                hsame name (append provenance unit) ∧
                  BEDC.FKernel.Package.PkgSig bundle lawRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
                      (fun row : BHist =>
                        hsame row lawRead ∧ hsame associativity (append hom composition))
                      (fun row : BHist =>
                        hsame row lawRead ∧ hsame unit identity ∧
                          BEDC.FKernel.Package.PkgSig bundle lawRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig
  intro carrier lawRoute lawPkg
  obtain ⟨unaryObject, identityCarrier, compositionRoute, associativitySame, unitSame,
    nameSame⟩ := carrier
  have sourceLaw :
      (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        lawRead := by
    exact ⟨hsame_refl lawRead, lawRoute⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row lawRead ∧ Cont associativity unit lawRead)
        (fun row : BHist => hsame row lawRead ∧ hsame associativity (append hom composition))
        (fun row : BHist =>
          hsame row lawRead ∧ hsame unit identity ∧
            BEDC.FKernel.Package.PkgSig bundle lawRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lawRead sourceLaw
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
        exact ⟨source.left, associativitySame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, unitSame, lawPkg⟩
    }
  exact
    ⟨unaryObject, identityCarrier, compositionRoute, lawRoute, associativitySame, unitSame,
      nameSame, lawPkg, cert⟩

theorem KernelCategoryCarrier_package_provenance_nonescape
    [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name provenanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      hsame provenanceRead provenance ->
        PkgSig bundle provenanceRead pkg ->
          UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
            Cont identity composition hom ∧ hsame provenanceRead provenance ∧
              hsame name (append provenance unit) ∧ PkgSig bundle provenanceRead pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row provenanceRead ∧
                    PkgSig bundle provenanceRead pkg)
                  (fun row : BHist => hsame row provenanceRead ∧
                    Cont identity composition hom)
                  (fun row : BHist => hsame row provenanceRead ∧
                    hsame name (append provenance unit) ∧
                      PkgSig bundle provenanceRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig
  intro carrier provenanceSame provenancePkg
  obtain ⟨unaryObject, identityCarrier, compositionRoute, _associativitySame,
    _unitSame, nameSame⟩ := carrier
  have sourceProvenance :
      (fun row : BHist => hsame row provenanceRead ∧
        PkgSig bundle provenanceRead pkg) provenanceRead := by
    exact ⟨hsame_refl provenanceRead, provenancePkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenanceRead ∧
          PkgSig bundle provenanceRead pkg)
        (fun row : BHist => hsame row provenanceRead ∧
          Cont identity composition hom)
        (fun row : BHist => hsame row provenanceRead ∧
          hsame name (append provenance unit) ∧ PkgSig bundle provenanceRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro provenanceRead sourceProvenance
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
        exact ⟨source.left, compositionRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, nameSame, source.right⟩
    }
  exact
    ⟨unaryObject, identityCarrier, compositionRoute, provenanceSame, nameSame,
      provenancePkg, cert⟩

end BEDC.Derived.KernelCategoryUp
