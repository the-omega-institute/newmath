import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_critical_strip_origin
    {Z S M R Q H C P N stripRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        SemanticNameCert
            (fun row : BHist => hsame row stripRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row Z ∨ hsame row S ∨ hsame row stripRead)
            (fun row : BHist => hsame row stripRead ∧ Cont Z S stripRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory stripRead ∧
            hsame H (append Z S) ∧ Cont Z S stripRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stripRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row Z ∨ hsame row S ∨ hsame row stripRead)
          (fun row : BHist => hsame row stripRead ∧ Cont Z S stripRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stripRead ⟨hsame_refl stripRead, stripUnary⟩
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
      exact ⟨source.left, stripRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, stripUnary, sameH, stripRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
