import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_row_source_scope
    {Z S M R Q H C P N zeroRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        SemanticNameCert
            (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row Z ∨ hsame row S ∨ hsame row zeroRead)
            (fun row : BHist => hsame row zeroRead ∧ Cont Z S zeroRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory zeroRead ∧
            hsame H (append Z S) ∧ Cont Z S zeroRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row Z ∨ hsame row S ∨ hsame row zeroRead)
          (fun row : BHist => hsame row zeroRead ∧ Cont Z S zeroRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroRead ⟨hsame_refl zeroRead, zeroUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, zeroRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, zeroUnary, sameH, zeroRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
