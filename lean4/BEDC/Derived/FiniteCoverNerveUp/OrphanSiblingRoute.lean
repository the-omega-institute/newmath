import BEDC.Derived.FiniteCoverNerveUp.NameCertObligations

namespace BEDC.Derived.FiniteCoverNerveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteCoverNerveOrphanSiblingRoute [AskSetup] [PackageSetup]
    {cover member overlap face radius fold uniform transport replay provenance name
      siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCoverNerveCarrier cover member overlap face radius fold uniform transport replay
        provenance name bundle pkg ->
      Cont uniform replay siblingRead ->
        PkgSig bundle siblingRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cover ∨ hsame row member ∨ hsame row overlap ∨
                  hsame row face ∨ hsame row radius ∨ hsame row fold ∨
                    hsame row uniform ∨ hsame row siblingRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont uniform replay siblingRead ∧
                  PkgSig bundle siblingRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory siblingRead := by
  -- BEDC touchpoint anchor: FiniteCoverNerveCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro nerveCarrier uniformReplaySibling siblingPkg
  obtain ⟨_coverUnary, _memberUnary, _overlapUnary, _faceUnary, _radiusUnary,
    _foldUnary, uniformUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _coverMemberOverlap, _overlapFaceRadius, _radiusFoldUniform, provenancePkg,
    _namePkg⟩ := nerveCarrier
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed uniformUnary replayUnary uniformReplaySibling
  have sourceSibling :
      (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row) siblingRead := by
    exact ⟨hsame_refl siblingRead, siblingUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row member ∨ hsame row overlap ∨ hsame row face ∨
              hsame row radius ∨ hsame row fold ∨ hsame row uniform ∨
                hsame row siblingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont uniform replay siblingRead ∧
              PkgSig bundle siblingRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro siblingRead sourceSibling
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, uniformReplaySibling, siblingPkg, provenancePkg⟩
  }
  exact ⟨cert, siblingUnary⟩

end BEDC.Derived.FiniteCoverNerveUp
