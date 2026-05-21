import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_gamma_real_dependency
    {Z S M R Q H C P N realRead gammaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R realRead ->
        Cont realRead Q gammaRead ->
          SemanticNameCert
              (fun row : BHist => hsame row gammaRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row gammaRead)
              (fun row : BHist => hsame row gammaRead ∧ Cont realRead Q gammaRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory realRead ∧
              UnaryHistory gammaRead ∧ hsame H (append Z S) ∧ Cont M R realRead ∧
                Cont realRead Q gammaRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet realRoute gammaRoute
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
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryM unaryR realRoute
  have gammaUnary : UnaryHistory gammaRead :=
    unary_cont_closed realUnary unaryQ gammaRoute
  have sourceAtGamma : hsame gammaRead gammaRead ∧ UnaryHistory gammaRead :=
    ⟨hsame_refl gammaRead, gammaUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gammaRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row gammaRead)
          (fun row : BHist => hsame row gammaRead ∧ Cont realRead Q gammaRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gammaRead sourceAtGamma
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, gammaRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, realUnary, gammaUnary, sameH, realRoute, gammaRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
