import BEDC.Derived.TwinSubstrateBoundaryClassifierUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TwinSubstrateBoundaryClassifierUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem TwinSubstrateBoundaryClassifierRefusalDiscipline
    {M G Q L D H C P N refusedRead : BHist} :
    Cont Q L refusedRead ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              FieldFaithful.fields
                (TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N) =
                [M, G, Q, L, D, H, C, P, N])
          (fun row : BHist => hsame row Q ∨ hsame row L ∨ hsame row D ∨ hsame row N)
          (fun row : BHist => hsame row N ∧ hsame L L ∧ Cont Q L refusedRead)
          hsame ∧
        FieldFaithful.fields (TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N) =
          [M, G, Q, L, D, H, C, P, N] ∧
        Cont Q L refusedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert FieldFaithful
  intro refusalRoute
  have fields_eq :
      FieldFaithful.fields (TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N) =
        [M, G, Q, L, D, H, C, P, N] := by
    rfl
  have sourceName :
      (fun row : BHist =>
        hsame row N ∧
          FieldFaithful.fields
            (TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N) =
            [M, G, Q, L, D, H, C, P, N]) N := by
    exact ⟨hsame_refl N, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧
            FieldFaithful.fields
              (TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N) =
              [M, G, Q, L, D, H, C, P, N])
        (fun row : BHist => hsame row Q ∨ hsame row L ∨ hsame row D ∨ hsame row N)
        (fun row : BHist => hsame row N ∧ hsame L L ∧ Cont Q L refusedRead)
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, hsame_refl L, refusalRoute⟩
    }
  exact ⟨cert, fields_eq, refusalRoute⟩

end BEDC.Derived.TwinSubstrateBoundaryClassifierUp
