import BEDC.Derived.CofinalModulusSealUp.RegSeqRatWindowFactorization
import BEDC.Derived.CofinalModulusSealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CofinalModulusSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CofinalModulusSealWindowBudgetExactness
    {budget modulus window limit regSeq stream dyadic real transport replay provenance name
      streamRead dyadicRead regSeqRead : BHist} :
    Cont budget window streamRead →
      Cont budget window dyadicRead →
        Cont budget window regSeqRead →
          SemanticNameCert
              (fun row : BHist =>
                hsame row streamRead ∨ hsame row dyadicRead ∨ hsame row regSeqRead)
              (fun row : BHist =>
                hsame row budget ∨ hsame row window ∨ hsame row streamRead ∨
                  hsame row dyadicRead ∨ hsame row regSeqRead)
              (fun _row : BHist =>
                Cont budget window streamRead ∧ Cont budget window dyadicRead ∧
                  Cont budget window regSeqRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro streamRoute dyadicRoute regSeqRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro streamRead (Or.inl (hsame_refl streamRead))
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
        cases source with
        | inl sameStream =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameStream)
        | inr rest =>
            cases rest with
            | inl sameDyadic =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic))
            | inr sameRegSeq =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRegSeq))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameStream =>
          exact Or.inr (Or.inr (Or.inl sameStream))
      | inr rest =>
          cases rest with
          | inl sameDyadic =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadic)))
          | inr sameRegSeq =>
              exact Or.inr (Or.inr (Or.inr (Or.inr sameRegSeq)))
    ledger_sound := by
      intro _row _source
      exact ⟨streamRoute, dyadicRoute, regSeqRoute⟩
  }

end BEDC.Derived.CofinalModulusSealUp
