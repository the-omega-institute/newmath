import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def HausdorffizationUp : Prop :=
  True

theorem HausdorffizationCarrier_namecert_obligations (P S M C W R E T K G N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
          hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
            hsame row N)
      (fun row : BHist =>
        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
          hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
            hsame row N)
      (fun row : BHist =>
        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
          hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
            hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro P (Or.inl (hsame_refl P))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem HausdorffizationCarrier_separated_reflection_boundary
    {P S M C W R E T K G N boundaryRead completionRead : BHist} :
    Cont P S boundaryRead →
      Cont M C completionRead →
        SemanticNameCert
          (fun row : BHist => hsame row S ∨ hsame row boundaryRead)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row boundaryRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            (hsame row S ∨ hsame row boundaryRead) ∧ Cont P S boundaryRead ∧
              Cont M C completionRead)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert NameCert
  intro hBoundary hCompletion
  exact {
    core := {
      carrier_inhabited := Exists.intro S (Or.inl (hsame_refl S))
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
        intro row other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameS =>
          exact Or.inr (Or.inl sameS)
      | inr sameBoundary =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBoundary)))))))
    ledger_sound := by
      intro row source
      exact And.intro source (And.intro hBoundary hCompletion)
  }

end BEDC.Derived
