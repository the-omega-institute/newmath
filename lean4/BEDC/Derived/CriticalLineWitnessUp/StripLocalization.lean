import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_strip_localization
    {Z S M R Q H C P N stripRead depthRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M Q depthRead ->
          Cont depthRead R comparisonRead ->
            SemanticNameCert
                (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row comparisonRead ∧ Cont Z S stripRead)
                (fun row : BHist =>
                  hsame row comparisonRead ∧ Cont depthRead R comparisonRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory stripRead ∧
                  UnaryHistory depthRead ∧ UnaryHistory comparisonRead ∧
                    hsame H (append Z S) ∧ Cont Z S stripRead ∧ Cont M R Q ∧
                      Cont M Q depthRead ∧ Cont depthRead R comparisonRead ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute depthRoute comparisonRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryQ depthRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed depthUnary unaryR comparisonRoute
  have sourceAtComparison :
      (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row) comparisonRead :=
    ⟨hsame_refl comparisonRead, comparisonUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row comparisonRead ∧ Cont Z S stripRead)
          (fun row : BHist =>
            hsame row comparisonRead ∧ Cont depthRead R comparisonRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead sourceAtComparison
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
      exact ⟨source.left, comparisonRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, stripUnary, depthUnary,
      comparisonUnary, sameH, stripRoute, routeQ, depthRoute, comparisonRoute, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
