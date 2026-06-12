import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_source_real_readback_factorization
    {Z S M R Q H C P N zeroSource realRead combinedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q zeroSource ->
        Cont M R realRead ->
          Cont zeroSource realRead combinedRead ->
            SemanticNameCert
                (fun row : BHist => hsame row combinedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row zeroSource ∨
                      hsame row realRead ∨ hsame row combinedRead)
                (fun row : BHist =>
                  hsame row combinedRead ∧ Cont zeroSource realRead combinedRead ∧
                    hsame H (append Z S))
                hsame ∧
              UnaryHistory zeroSource ∧ UnaryHistory realRead ∧ UnaryHistory combinedRead ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroSourceRoute realReadRoute combinedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have zeroSourceUnary : UnaryHistory zeroSource :=
    unary_cont_closed sourceUnary unaryQ zeroSourceRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realReadRoute
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed zeroSourceUnary realReadUnary combinedRoute
  have sourceAtCombined : hsame combinedRead combinedRead ∧ UnaryHistory combinedRead :=
    ⟨hsame_refl combinedRead, combinedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row combinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row zeroSource ∨ hsame row realRead ∨
                hsame row combinedRead)
          (fun row : BHist =>
            hsame row combinedRead ∧ Cont zeroSource realRead combinedRead ∧
              hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro combinedRead sourceAtCombined
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
      exact ⟨source.left, combinedRoute, sameH⟩
  }
  exact ⟨cert, zeroSourceUnary, realReadUnary, combinedUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
