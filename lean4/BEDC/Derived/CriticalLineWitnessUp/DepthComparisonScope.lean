import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_depth_comparison_scope
    {Z S M R Q H C P N zeroRead depthRead comparisonRead scopedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R depthRead ->
          Cont depthRead Q comparisonRead ->
            Cont comparisonRead N scopedRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row scopedRead ∧ Cont Z S zeroRead ∧ Cont M R depthRead)
                  (fun row : BHist =>
                    hsame row scopedRead ∧ Cont depthRead Q comparisonRead ∧
                      Cont comparisonRead N scopedRead)
                  hsame ∧
                UnaryHistory zeroRead ∧ UnaryHistory depthRead ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory scopedRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute depthRoute comparisonRoute scopedRoute
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
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed depthUnary unaryQ comparisonRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed comparisonUnary unaryN scopedRoute
  have sourceAtScope : hsame scopedRead scopedRead ∧ UnaryHistory scopedRead :=
    ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scopedRead ∧ Cont Z S zeroRead ∧ Cont M R depthRead)
          (fun row : BHist =>
            hsame row scopedRead ∧ Cont depthRead Q comparisonRead ∧
              Cont comparisonRead N scopedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceAtScope
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
      exact ⟨source.left, zeroRoute, depthRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, comparisonRoute, scopedRoute⟩
  }
  exact
    ⟨cert, zeroUnary, depthUnary, comparisonUnary, scopedUnary, sameH, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
