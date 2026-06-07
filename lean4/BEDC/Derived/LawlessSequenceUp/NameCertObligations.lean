import BEDC.Derived.LawlessSequenceUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LawlessSequenceNameCertObligations (x : LawlessSequenceUp) :
    ∃ W B I H C P N : BHist,
      x = LawlessSequenceUp.mk W B I H C P N ∧
        SemanticNameCert
          (fun row : BHist => hsame row N)
          (fun row : BHist =>
            hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
          hsame ∧
          Cont BHist.Empty W W ∧ Cont BHist.Empty B B ∧ Cont BHist.Empty I I := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  cases x with
  | mk W B I H C P N =>
      let rowSurface := fun row : BHist =>
        hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
          hsame row P ∨ hsame row N
      have nameCert :
          SemanticNameCert (fun row : BHist => hsame row N) rowSurface rowSurface hsame := {
        core := {
          carrier_inhabited := Exists.intro N (hsame_refl N)
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
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source)))))
        ledger_sound := by
          intro _row source
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source)))))
      }
      exact
        ⟨W, B, I, H, C, P, N, rfl, nameCert, cont_left_unit W, cont_left_unit B,
          cont_left_unit I⟩

end BEDC.Derived.LawlessSequenceUp
