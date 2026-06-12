import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_stdbridge_premise_surface
    {Z S M R Q H C P N image readback premise : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q image ->
        Cont C P readback ->
          Cont image readback premise ->
            SemanticNameCert
                (fun row : BHist => hsame row premise ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row image ∨
                      hsame row readback ∨ hsame row premise)
                (fun row : BHist =>
                  hsame row premise ∧ Cont image readback premise ∧ Cont C P readback)
                hsame ∧
              UnaryHistory image ∧ UnaryHistory readback ∧ UnaryHistory premise ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet imageRoute readbackRoute premiseRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have imageUnary : UnaryHistory image :=
    unary_cont_closed sourceUnary unaryQ imageRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed unaryC unaryP readbackRoute
  have premiseUnary : UnaryHistory premise :=
    unary_cont_closed imageUnary readbackUnary premiseRoute
  have sourceAtPremise : hsame premise premise ∧ UnaryHistory premise :=
    ⟨hsame_refl premise, premiseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row premise ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row image ∨ hsame row readback ∨ hsame row premise)
          (fun row : BHist =>
            hsame row premise ∧ Cont image readback premise ∧ Cont C P readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro premise sourceAtPremise
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, premiseRoute, readbackRoute⟩
  }
  exact ⟨cert, imageUnary, readbackUnary, premiseUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
