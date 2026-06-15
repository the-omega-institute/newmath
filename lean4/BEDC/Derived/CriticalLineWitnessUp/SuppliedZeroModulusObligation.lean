import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_supplied_zero_modulus_obligation
    {Z S M R Q H C P N zeroRead modulusRead obligationRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q modulusRead ->
          Cont modulusRead N obligationRead ->
            SemanticNameCert
                (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row obligationRead)
                (fun row : BHist =>
                  hsame row obligationRead ∧ Cont zeroRead Q modulusRead ∧
                    Cont modulusRead N obligationRead)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧
                UnaryHistory obligationRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N ∧ Cont Z S zeroRead ∧
                    Cont zeroRead Q modulusRead ∧ Cont modulusRead N obligationRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute modulusRoute obligationRoute
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
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zeroUnary unaryQ modulusRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed modulusUnary unaryN obligationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row obligationRead)
          (fun row : BHist =>
            hsame row obligationRead ∧ Cont zeroRead Q modulusRead ∧
              Cont modulusRead N obligationRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRead ⟨hsame_refl obligationRead, obligationUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute, obligationRoute⟩
  }
  exact
    ⟨cert, zeroUnary, modulusUnary, obligationUnary, sameH, routeQ, routeC, routeN,
      zeroRoute, modulusRoute, obligationRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
