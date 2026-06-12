import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRegSeqRatRealModulusHandoff
    {Z S M R Q H C P N regRead realRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Q H regRead →
        Cont regRead C realRead →
          SemanticNameCert
              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row regRead ∨
                  hsame row realRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Q H regRead ∧ Cont regRead C realRead)
              hsame ∧
            UnaryHistory regRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet regRoute realRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed unaryQ unaryH regRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regUnary unaryC realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row regRead ∨
              hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q H regRead ∧ Cont regRead C realRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
      exact ⟨source.right, regRoute, realRoute⟩
  }
  exact ⟨cert, regUnary, realUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
