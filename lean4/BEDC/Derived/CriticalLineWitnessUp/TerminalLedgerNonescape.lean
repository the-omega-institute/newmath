import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CriticalLineWitnessTerminalLedgerNonescape
    {Z S M R Q H C P N terminalRead : BHist} :
    Cont Z S M ->
      Cont M R Q ->
        Cont Q H terminalRead ->
          SemanticNameCert
            (fun row : BHist => hsame row terminalRead)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row terminalRead)
            (fun row : BHist =>
              hsame row terminalRead ∧ Cont Z S M ∧ Cont M R Q ∧ Cont Q H terminalRead)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro zsmRoute mrqRoute qhTerminalRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro terminalRead (hsame_refl terminalRead)
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
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source, zsmRoute, mrqRoute, qhTerminalRoute⟩
  }

end BEDC.Derived.CriticalLineWitnessUp
