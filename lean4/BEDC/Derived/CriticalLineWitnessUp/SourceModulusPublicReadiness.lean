import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_public_readiness
    {Z S M R Q H C P N sourceRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead Q modulusRead ->
          SemanticNameCert
              (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row sourceRead ∨ hsame row modulusRead ∨ hsame row N)
              (fun row : BHist => hsame row modulusRead ∧ Cont sourceRead Q modulusRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory sourceRead ∧
              UnaryHistory modulusRead ∧ hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                Cont sourceRead Q modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute sourceModulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary unaryQ sourceModulusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row sourceRead ∨ hsame row modulusRead ∨ hsame row N)
          (fun row : BHist => hsame row modulusRead ∧ Cont sourceRead Q modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead
        ⟨hsame_refl modulusRead, modulusUnary⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sourceModulusRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, sourceUnary, modulusUnary, sameH, sourceRoute,
      sourceModulusRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
