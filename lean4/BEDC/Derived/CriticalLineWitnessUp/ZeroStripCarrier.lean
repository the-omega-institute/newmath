import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_carrier
    {Z S M R Q H C P N zeroStripRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        SemanticNameCert
            (fun row : BHist => hsame row zeroStripRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row Z ∨ hsame row S ∨ hsame row zeroStripRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont Z S zeroStripRead ∧ hsame H (append Z S))
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory zeroStripRead ∧
            hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have sourceAtZero : hsame zeroStripRead zeroStripRead ∧ UnaryHistory zeroStripRead :=
    ⟨hsame_refl zeroStripRead, zeroUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroStripRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row Z ∨ hsame row S ∨ hsame row zeroStripRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zeroStripRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroStripRead sourceAtZero
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
      exact ⟨source.right, zeroRoute, sameH⟩
  }
  exact ⟨cert, unaryZ, unaryS, zeroUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
