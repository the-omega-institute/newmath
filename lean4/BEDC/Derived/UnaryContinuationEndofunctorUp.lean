import BEDC.Derived.CategoryUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UnaryContinuationEndofunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

def UnaryContinuationEndofunctorCarrier
    (object hom action identity composition transport route provenance localName : BHist) :
    Prop :=
  UnaryHistory object ∧ UnaryHistory hom ∧ UnaryHistory action ∧ UnaryHistory identity ∧
    UnaryHistory composition ∧
      Cont object action transport ∧
        Cont hom identity route ∧
          Cont composition transport provenance ∧ hsame provenance localName

theorem UnaryContinuationEndofunctorCarrier_composition_stability
    {object hom action identity composition transport route provenance localName source mid target f g
      fg imageF imageG imageFG imageComp : BHist} :
    UnaryContinuationEndofunctorCarrier object hom action identity composition transport route
      provenance localName ->
      CategoryHomCarrier source mid f ->
        CategoryHomCarrier mid target g ->
          Cont f g fg ->
            Cont action f imageF ->
              Cont action g imageG ->
                Cont action fg imageFG ->
                  Cont imageF imageG imageComp ->
                    hsame imageFG imageComp ->
                      CategoryHomCarrier source target fg ∧ UnaryHistory imageFG ∧
                        UnaryHistory imageComp ∧ hsame imageFG imageComp := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier UnaryHistory
  intro _carrier left right comp actionF actionG actionFG imageCompRel sameImage
  have composite : CategoryHomCarrier source target fg :=
    CategoryHomCarrier_comp_closed left right comp
  have actionUnary : UnaryHistory action := _carrier.right.right.left
  have imageFGUnary : UnaryHistory imageFG :=
    unary_cont_closed actionUnary composite.right.right.left actionFG
  have imageFUnary : UnaryHistory imageF :=
    unary_cont_closed actionUnary left.right.right.left actionF
  have imageGUnary : UnaryHistory imageG :=
    unary_cont_closed actionUnary right.right.right.left actionG
  have imageCompUnary : UnaryHistory imageComp :=
    unary_cont_closed imageFUnary imageGUnary imageCompRel
  exact And.intro composite
    (And.intro imageFGUnary (And.intro imageCompUnary sameImage))

theorem UnaryContinuationEndofunctor_namecert_obligations [AskSetup] [PackageSetup]
    {O H F I M T C P N objectRead identityRead compositionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContinuationEndofunctorCarrier O H F I M T C P N ->
      Cont O F objectRead ->
        Cont H I identityRead ->
          Cont M T compositionRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row N ∧ Cont O F objectRead ∧ Cont H I identityRead ∧
                    Cont M T compositionRead)
                (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                hsame ∧ UnaryHistory objectRead ∧ UnaryHistory identityRead ∧
                UnaryHistory compositionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier objectRoute identityRoute compositionRoute provenancePkg
  obtain ⟨objectUnary, homUnary, actionUnary, identityUnary, compositionUnary,
    objectActionTransport, homIdentityRoute, compositionTransportProvenance,
    sameProvenanceName⟩ := carrier
  have transportUnary : UnaryHistory T :=
    unary_cont_closed objectUnary actionUnary objectActionTransport
  have provenanceUnary : UnaryHistory P :=
    unary_cont_closed compositionUnary transportUnary compositionTransportProvenance
  have nameUnary : UnaryHistory N :=
    unary_transport provenanceUnary sameProvenanceName
  have objectReadUnary : UnaryHistory objectRead :=
    unary_cont_closed objectUnary actionUnary objectRoute
  have identityReadUnary : UnaryHistory identityRead :=
    unary_cont_closed homUnary identityUnary identityRoute
  have compositionReadUnary : UnaryHistory compositionRead :=
    unary_cont_closed compositionUnary transportUnary compositionRoute
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nameUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row N ∧ Cont O F objectRead ∧ Cont H I identityRead ∧
            Cont M T compositionRead)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, objectRoute, identityRoute, compositionRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, objectReadUnary, identityReadUnary, compositionReadUnary⟩

theorem UnaryContinuationEndofunctorCarrier_identity_stability
    {object hom action identity composition transport route provenance localName a imageObject e
      imageE : BHist} :
    UnaryContinuationEndofunctorCarrier object hom action identity composition transport route
        provenance localName →
      CategoryHomCarrier a a e →
        Cont action a imageObject →
          Cont action e imageE →
            hsame imageE BHist.Empty →
              UnaryHistory imageObject ∧ UnaryHistory imageE ∧
                CategoryHomCarrier imageObject imageObject BHist.Empty ∧
                  Cont action e imageE ∧ hsame imageE BHist.Empty := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier UnaryHistory
  intro carrier identityHom objectAction homAction sameImageEmpty
  obtain ⟨_objectUnary, _homUnary, actionUnary, _identityUnary, _compositionUnary,
    _objectActionTransport, _homIdentityRoute, _compositionTransportProvenance,
    _sameProvenanceName⟩ := carrier
  have unaryA : UnaryHistory a := identityHom.left
  have unaryE : UnaryHistory e := identityHom.right.right.left
  have imageObjectUnary : UnaryHistory imageObject :=
    unary_cont_closed actionUnary unaryA objectAction
  have imageEUnary : UnaryHistory imageE :=
    unary_cont_closed actionUnary unaryE homAction
  have imageIdentity : CategoryHomCarrier imageObject imageObject BHist.Empty :=
    CategoryHomCarrier_empty_identity imageObjectUnary
  exact ⟨imageObjectUnary, imageEUnary, imageIdentity, homAction, sameImageEmpty⟩

end BEDC.Derived.UnaryContinuationEndofunctorUp
