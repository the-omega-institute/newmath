import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessObstructionSeparation
    {Z S M R Q H C P N obstructionRead fixedRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S obstructionRead →
        Cont obstructionRead N fixedRead →
          Cont fixedRead Q refusalRead →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row obstructionRead ∨
                    hsame row fixedRead ∨ hsame row refusalRead)
                (fun row : BHist =>
                  hsame row refusalRead ∧ Cont Z S obstructionRead ∧
                    Cont obstructionRead N fixedRead ∧ Cont fixedRead Q refusalRead)
                hsame ∧
              UnaryHistory obstructionRead ∧ UnaryHistory fixedRead ∧
                UnaryHistory refusalRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet obstructionRoute fixedRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed unaryZ unaryS obstructionRoute
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed obstructionUnary unaryN fixedRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed fixedUnary unaryQ refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row obstructionRead ∨
              hsame row fixedRead ∨ hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont Z S obstructionRead ∧
              Cont obstructionRead N fixedRead ∧ Cont fixedRead Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact ⟨source.left, obstructionRoute, fixedRoute, refusalRoute⟩
  }
  exact ⟨cert, obstructionUnary, fixedUnary, refusalUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
