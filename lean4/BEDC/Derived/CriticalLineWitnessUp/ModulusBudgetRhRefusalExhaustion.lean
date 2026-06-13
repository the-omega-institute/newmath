import BEDC.Derived.CriticalLineWitnessUp
import BEDC.Derived.CriticalLineWitnessUp.ModulusRefusalScope

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_budget_rh_refusal_exhaustion
    {Z S M R Q H C P N modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R modulusRead →
        Cont N Q refusalRead →
          SemanticNameCert
              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row refusalRead ∧ Cont M R modulusRead)
              (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory N ∧
              UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                Cont M R Q ∧ Cont M R modulusRead ∧ Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet modulusRoute refusalRoute
  have scope :
      UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory N ∧
        UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
          Cont M R Q :=
    CriticalLineWitnessCarrier_modulus_refusal_scope packet modulusRoute refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead ∧ Cont M R modulusRead)
          (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead
        ⟨hsame_refl refusalRead, scope.right.right.right.right.right.left⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, scope.left, scope.right.left, scope.right.right.left,
      scope.right.right.right.left, scope.right.right.right.right.left,
      scope.right.right.right.right.right.left,
      scope.right.right.right.right.right.right.left,
      scope.right.right.right.right.right.right.right, modulusRoute, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
