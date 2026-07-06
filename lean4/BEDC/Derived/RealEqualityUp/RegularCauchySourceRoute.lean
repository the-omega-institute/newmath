import BEDC.Derived.RealEqualityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealEqualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealEqualityCarrier_regular_cauchy_source_route [AskSetup] [PackageSetup]
    {leftSeal rightSeal leftWindow rightWindow leftRead rightRead sharedWindow tolerance
      uniformity classifier transport replay provenance localName sourceRoute sealRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealEqualityCarrier leftSeal rightSeal leftWindow rightWindow leftRead rightRead
        sharedWindow tolerance uniformity classifier transport replay provenance localName
        bundle pkg ->
      Cont leftRead rightRead sourceRoute ->
        Cont sourceRoute tolerance sealRoute ->
          hsame sealRoute classifier ->
            PkgSig bundle provenance pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row classifier ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row leftRead ∨ hsame row rightRead ∨ hsame row sharedWindow ∨
                      hsame row tolerance ∨ hsame row uniformity ∨ hsame row classifier ∨
                        hsame row provenance ∨ hsame row localName)
                  (fun _row : BHist =>
                    Cont leftRead rightRead sourceRoute ∧
                      Cont sourceRoute tolerance sealRoute ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory sourceRoute ∧ UnaryHistory sealRoute ∧
                  UnaryHistory classifier := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier readSource sourceSeal sameSealClassifier provenancePkg
  obtain ⟨_leftSealUnary, _rightSealUnary, _leftWindowUnary, _rightWindowUnary,
    leftReadUnary, rightReadUnary, _sharedWindowUnary, toleranceUnary, _uniformityUnary,
    classifierUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _carrierProvenancePkg, _localNamePkg⟩ := carrier
  have sourceRouteUnary : UnaryHistory sourceRoute :=
    unary_cont_closed leftReadUnary rightReadUnary readSource
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed sourceRouteUnary toleranceUnary sourceSeal
  have classifierUnaryFromRoute : UnaryHistory classifier :=
    unary_transport sealRouteUnary sameSealClassifier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row leftRead ∨ hsame row rightRead ∨ hsame row sharedWindow ∨
              hsame row tolerance ∨ hsame row uniformity ∨ hsame row classifier ∨
                hsame row provenance ∨ hsame row localName)
          (fun _row : BHist =>
            Cont leftRead rightRead sourceRoute ∧ Cont sourceRoute tolerance sealRoute ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifier
        ⟨hsame_refl classifier, classifierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row _source
      exact ⟨readSource, sourceSeal, provenancePkg⟩
  }
  exact ⟨cert, sourceRouteUnary, sealRouteUnary, classifierUnaryFromRoute⟩

end BEDC.Derived.RealEqualityUp
