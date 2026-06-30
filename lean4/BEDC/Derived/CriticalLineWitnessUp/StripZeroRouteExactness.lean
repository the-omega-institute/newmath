import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_strip_zero_route_exactness
    {Z S M R Q H C P N stripRead routeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S stripRead →
        Cont stripRead H routeRead →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row routeRead ∧ Cont Z S stripRead)
              (fun row : BHist => hsame row routeRead ∧ Cont stripRead H routeRead)
              hsame ∧
            UnaryHistory stripRead ∧ UnaryHistory routeRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute routeRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have hUnary : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed stripUnary hUnary routeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row routeRead ∧ Cont Z S stripRead)
          (fun row : BHist => hsame row routeRead ∧ Cont stripRead H routeRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        have otherSame : hsame other routeRead :=
          hsame_trans (hsame_symm same) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right same
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, stripRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeRoute⟩
  }
  exact ⟨cert, stripUnary, routeUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
