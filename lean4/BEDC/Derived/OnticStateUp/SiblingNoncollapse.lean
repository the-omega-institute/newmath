import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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

theorem OnticStateSiblingNoncollapse [AskSetup] [PackageSetup]
    {S A K R H C P N siblingRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S A siblingRead →
      Cont R N auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row auditRead ∧
                  FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                    [S, A, K, R, H, C, P, N])
              (fun row : BHist =>
                hsame row S ∨ hsame row A ∨ hsame row K ∨ hsame row R ∨
                  (Cont S A siblingRead ∧ Cont R N row))
              (fun row : BHist =>
                hsame row auditRead ∧ PkgSig bundle auditRead pkg ∧ hsame R R)
              hsame ∧
            FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
              [S, A, K, R, H, C, P, N] ∧
              Cont S A siblingRead ∧ Cont R N auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro siblingRoute auditRoute packageAudit
  have fieldsExact :
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] := by
    rfl
  have sourceAudit :
      (fun row : BHist =>
        hsame row auditRead ∧
          FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
            [S, A, K, R, H, C, P, N]) auditRead := by
    exact ⟨hsame_refl auditRead, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row auditRead ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row K ∨ hsame row R ∨
              (Cont S A siblingRead ∧ Cont R N row))
          (fun row : BHist =>
            hsame row auditRead ∧ PkgSig bundle auditRead pkg ∧ hsame R R)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAudit
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨siblingRoute, auditRoute⟩)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageAudit, hsame_refl R⟩
  }
  exact ⟨cert, fieldsExact, siblingRoute, auditRoute⟩

end BEDC.Derived.OnticStateUp
