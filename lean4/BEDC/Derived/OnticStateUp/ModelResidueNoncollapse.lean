import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem OnticStateModelResidueNoncollapse [AskSetup] [PackageSetup]
    {S A K R H C P N modelRead quantumRead residueAudit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S A modelRead →
      Cont R N residueAudit →
        Cont modelRead quantumRead residueAudit →
          PkgSig bundle residueAudit pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row residueAudit ∧
                    FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                      [S, A, K, R, H, C, P, N])
                (fun row : BHist =>
                  hsame row R ∨ Cont R N residueAudit ∨
                    Cont modelRead quantumRead residueAudit)
                (fun row : BHist => hsame row residueAudit ∧ PkgSig bundle residueAudit pkg)
                hsame ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                  [S, A, K, R, H, C, P, N] ∧
                Cont R N residueAudit ∧ Cont modelRead quantumRead residueAudit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame FieldFaithful SemanticNameCert
  intro _modelRoute residueRoute modelQuantumRoute residuePkg
  have fieldsExact :
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] := by
    rfl
  have sourceAtResidue :
      hsame residueAudit residueAudit ∧
        FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
          [S, A, K, R, H, C, P, N] := by
    exact ⟨hsame_refl residueAudit, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row residueAudit ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist =>
            hsame row R ∨ Cont R N residueAudit ∨ Cont modelRead quantumRead residueAudit)
          (fun row : BHist => hsame row residueAudit ∧ PkgSig bundle residueAudit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residueAudit sourceAtResidue
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inl residueRoute)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, residuePkg⟩
  }
  exact ⟨cert, fieldsExact, residueRoute, modelQuantumRoute⟩

end BEDC.Derived.OnticStateUp
