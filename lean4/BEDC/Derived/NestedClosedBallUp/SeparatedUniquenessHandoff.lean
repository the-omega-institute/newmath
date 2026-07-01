import BEDC.Derived.NestedClosedBallUp.PublicExport

namespace BEDC.Derived.NestedClosedBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NestedClosedBallSeparatedUniquenessHandoff
    {M K F S R D E H C P N centerWindow readbackWindow dyadicSeal realSeal packageRead
      leftEndpoint rightEndpoint comparisonRead : BHist} :
    Cont F S centerWindow -> Cont centerWindow R readbackWindow ->
      Cont readbackWindow D dyadicSeal -> Cont dyadicSeal E realSeal ->
        Cont realSeal P packageRead -> Cont packageRead N leftEndpoint ->
          Cont packageRead K rightEndpoint -> Cont leftEndpoint rightEndpoint comparisonRead ->
            UnaryHistory F -> UnaryHistory S -> UnaryHistory R -> UnaryHistory D ->
              UnaryHistory E -> UnaryHistory P -> UnaryHistory N -> UnaryHistory K ->
                SemanticNameCert
                    (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row S ∨ hsame row R ∨
                        hsame row D ∨ hsame row E ∨ hsame row P ∨ hsame row N ∨
                          hsame row leftEndpoint ∨ hsame row rightEndpoint ∨
                            hsame row comparisonRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont realSeal P packageRead ∧
                        Cont packageRead N leftEndpoint ∧ Cont packageRead K rightEndpoint ∧
                          Cont leftEndpoint rightEndpoint comparisonRead)
                    hsame ∧ UnaryHistory leftEndpoint ∧ UnaryHistory rightEndpoint ∧
                      UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro centerRoute readbackRoute dyadicRoute realRoute packageRoute leftRoute rightRoute
    comparisonRoute fUnary sUnary rUnary dUnary eUnary pUnary nUnary kUnary
  have centerUnary : UnaryHistory centerWindow :=
    unary_cont_closed fUnary sUnary centerRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed centerUnary rUnary readbackRoute
  have dyadicUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed readbackUnary dUnary dyadicRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary eUnary realRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed realUnary pUnary packageRoute
  have leftUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed packageUnary nUnary leftRoute
  have rightUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed packageUnary kUnary rightRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed leftUnary rightUnary comparisonRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row F ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
            hsame row E ∨ hsame row P ∨ hsame row N ∨ hsame row leftEndpoint ∨
              hsame row rightEndpoint ∨ hsame row comparisonRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont realSeal P packageRead ∧
            Cont packageRead N leftEndpoint ∧ Cont packageRead K rightEndpoint ∧
              Cont leftEndpoint rightEndpoint comparisonRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead
        ⟨hsame_refl comparisonRead, comparisonUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packageRoute, leftRoute, rightRoute, comparisonRoute⟩
  }
  exact ⟨cert, leftUnary, rightUnary, comparisonUnary⟩

end BEDC.Derived.NestedClosedBallUp
