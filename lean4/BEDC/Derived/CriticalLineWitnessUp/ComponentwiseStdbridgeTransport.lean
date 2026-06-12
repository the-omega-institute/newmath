import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_componentwise_stdbridge_transport
    {Z S M R Q H C P N imageRead readbackRead bridgeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S imageRead ->
        Cont imageRead H readbackRead ->
          Cont readbackRead N bridgeRead ->
            SemanticNameCert
                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row imageRead ∨
                    hsame row readbackRead ∨ hsame row bridgeRead)
                (fun row : BHist => hsame row bridgeRead ∧ Cont readbackRead N bridgeRead)
                hsame ∧
              UnaryHistory imageRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory bridgeRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet imageRoute readbackRoute bridgeRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed unaryZ unaryS imageRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed imageUnary unaryH readbackRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed readbackUnary unaryN bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row imageRead ∨
              hsame row readbackRead ∨ hsame row bridgeRead)
          (fun row : BHist => hsame row bridgeRead ∧ Cont readbackRead N bridgeRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgeRoute⟩
  }
  exact ⟨cert, imageUnary, readbackUnary, bridgeUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
