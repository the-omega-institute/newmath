import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_strip_readback
    {Z S M R Q H C P N stripRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q readback ->
          SemanticNameCert
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun row : BHist => hsame row readback ∧ Cont Z S stripRead)
              (fun row : BHist => hsame row readback ∧ Cont stripRead Q readback)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory stripRead ∧
              UnaryHistory readback ∧ hsame H (append Z S) ∧ Cont Z S stripRead ∧
                Cont stripRead Q readback ∧ Cont M R Q ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed stripUnary unaryQ readbackRoute
  have sourceAtReadback : hsame readback readback ∧ UnaryHistory readback :=
    ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist => hsame row readback ∧ Cont Z S stripRead)
          (fun row : BHist => hsame row readback ∧ Cont stripRead Q readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceAtReadback
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
      exact ⟨source.left, stripRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, stripUnary, readbackUnary, sameH, stripRoute,
      readbackRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
