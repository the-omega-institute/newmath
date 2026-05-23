import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_depth_request_ledger
    {Z S M R Q H C P N depthRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R depthRead ->
        Cont depthRead Q comparisonRead ->
          SemanticNameCert
              (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row comparisonRead)
              (fun row : BHist =>
                hsame row comparisonRead ∧ Cont depthRead Q comparisonRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory depthRead ∧
                UnaryHistory comparisonRead ∧ hsame H (append Z S) ∧
                  Cont M R depthRead ∧ Cont depthRead Q comparisonRead ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet depthRoute comparisonRoute
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
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed depthUnary unaryQ comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row comparisonRead)
          (fun row : BHist => hsame row comparisonRead ∧ Cont depthRead Q comparisonRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comparisonRead ⟨hsame_refl comparisonRead, comparisonUnary⟩
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
      exact ⟨source.left, comparisonRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, depthUnary,
      comparisonUnary, sameH, depthRoute, comparisonRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
