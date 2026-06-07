import BEDC.Derived.RegularCauchyDiagonalMeetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyDiagonalMeetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RegularCauchyDiagonalMeetNonescape (x : RegularCauchyDiagonalMeetUp) :
    ∃ T M E W Q H C P N : BHist,
      x = RegularCauchyDiagonalMeetUp.mk T M E W Q H C P N ∧
        Cont M T (append M T) ∧
          Cont (append M T) E (append (append M T) E) ∧
            Cont (append (append M T) E) W (append (append (append M T) E) W) ∧
              SemanticNameCert
                (fun row : BHist => hsame row Q)
                (fun row : BHist =>
                  hsame row T ∨ hsame row M ∨ hsame row E ∨ hsame row W ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N)
                (fun row : BHist => hsame row Q)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  cases x with
  | mk T M E W Q H C P N =>
      exact
        ⟨T, M, E, W, Q, H, C, P, N, rfl, cont_intro rfl, cont_intro rfl,
          cont_intro rfl,
          {
            core := {
              carrier_inhabited := Exists.intro Q (hsame_refl Q)
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
                intro _row _other sameRows sourceRow
                exact hsame_trans (hsame_symm sameRows) sourceRow
            }
            pattern_sound := by
              intro _row sourceRow
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sourceRow))))
            ledger_sound := by
              intro _row sourceRow
              exact sourceRow
          }⟩

end BEDC.Derived.RegularCauchyDiagonalMeetUp
