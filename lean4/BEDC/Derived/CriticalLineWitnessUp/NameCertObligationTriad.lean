import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_namecert_obligation_triad {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      SemanticNameCert
          (fun row : BHist => CriticalLineWitnessCarrier Z S M R Q H C P N ∧ hsame row N)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ hsame row N)
          hsame ∧
        UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨unaryQ, unaryC, unaryN, sameH⟩ :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  have cert :
      SemanticNameCert
          (fun row : BHist => CriticalLineWitnessCarrier Z S M R Q H C P N ∧ hsame row N)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ hsame row N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨packet, hsame_refl N⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
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
                      (Or.inr source.right)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport unaryN (hsame_symm source.right), source.right⟩
  }
  exact ⟨cert, unaryQ, unaryC, unaryN, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
