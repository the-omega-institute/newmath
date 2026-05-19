import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem OnticStateNameCertObligationSurface
    {S A K R H C P N accessResidue : BHist} :
    Cont A R accessResidue →
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row K ∨ hsame row R ∨
              hsame row accessResidue ∨ hsame row N)
          (fun row : BHist => hsame row N ∧ Cont A R accessResidue)
          hsame ∧
        FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
          [S, A, K, R, H, C, P, N] ∧
          Cont A R accessResidue := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldFaithful SemanticNameCert
  intro accessRoute
  have fieldsExact :
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] := by
    rfl
  have sourceN :
      (fun row : BHist =>
        hsame row N ∧
          FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
            [S, A, K, R, H, C, P, N]) N := by
    exact ⟨hsame_refl N, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row K ∨ hsame row R ∨
              hsame row accessResidue ∨ hsame row N)
          (fun row : BHist => hsame row N ∧ Cont A R accessResidue)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceN
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, accessRoute⟩
    }
  exact ⟨cert, fieldsExact, accessRoute⟩

end BEDC.Derived.OnticStateUp
