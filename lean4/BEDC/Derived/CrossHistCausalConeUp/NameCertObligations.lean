import BEDC.Derived.CrossHistCausalConeUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CrossHistCausalConeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem CrossHistCausalConeNameCert_obligations
    {A B K W R M S H C P N coneReplay : BHist} :
    Cont W R coneReplay ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              FieldFaithful.fields
                (CrossHistCausalConeUp.mk A B K W R M S H C P N) =
                [A, B, K, W, R, M, S, H, C, P, N])
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row K ∨ hsame row W ∨
              hsame row R ∨ hsame row M ∨ hsame row S ∨ hsame row N)
          (fun row : BHist => hsame row N ∧ Cont W R coneReplay)
          hsame ∧
        FieldFaithful.fields (CrossHistCausalConeUp.mk A B K W R M S H C P N) =
          [A, B, K, W, R, M, S, H, C, P, N] ∧
        Cont W R coneReplay := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert FieldFaithful
  intro coneRoute
  have fields_eq :
      FieldFaithful.fields (CrossHistCausalConeUp.mk A B K W R M S H C P N) =
        [A, B, K, W, R, M, S, H, C, P, N] := by
    rfl
  have sourceName :
      (fun row : BHist =>
        hsame row N ∧
          FieldFaithful.fields
            (CrossHistCausalConeUp.mk A B K W R M S H C P N) =
            [A, B, K, W, R, M, S, H, C, P, N]) N := by
    exact ⟨hsame_refl N, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧
            FieldFaithful.fields
              (CrossHistCausalConeUp.mk A B K W R M S H C P N) =
              [A, B, K, W, R, M, S, H, C, P, N])
        (fun row : BHist =>
          hsame row A ∨ hsame row B ∨ hsame row K ∨ hsame row W ∨
            hsame row R ∨ hsame row M ∨ hsame row S ∨ hsame row N)
        (fun row : BHist => hsame row N ∧ Cont W R coneReplay)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceName
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
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, coneRoute⟩
    }
  exact ⟨cert, fields_eq, coneRoute⟩

end BEDC.Derived.CrossHistCausalConeUp
