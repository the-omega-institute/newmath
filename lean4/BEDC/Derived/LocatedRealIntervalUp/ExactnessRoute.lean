import BEDC.Derived.LocatedRealIntervalUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedRealIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LocatedRealIntervalCarrier_exactness_route
    {L U rho Delta Lambda M bracket endpointRead radiusRead dyadicIntervalRead
      locatorRead modulusRead bracketRead : BHist} :
    UnaryHistory L ->
      UnaryHistory U ->
        UnaryHistory rho ->
          UnaryHistory Delta ->
            UnaryHistory Lambda ->
              UnaryHistory M ->
                UnaryHistory bracket ->
                  Cont L U endpointRead ->
                    Cont endpointRead rho radiusRead ->
                      Cont radiusRead Delta dyadicIntervalRead ->
                        Cont dyadicIntervalRead Lambda locatorRead ->
                          Cont locatorRead M modulusRead ->
                            Cont modulusRead bracket bracketRead ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row bracketRead ∧
                                    UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row endpointRead ∨ hsame row radiusRead ∨
                                      hsame row dyadicIntervalRead ∨
                                        hsame row locatorRead ∨ hsame row modulusRead ∨
                                          hsame row bracketRead)
                                  (fun row : BHist =>
                                    hsame row bracketRead ∧
                                      Cont modulusRead bracket bracketRead)
                                  hsame ∧
                                UnaryHistory endpointRead ∧ UnaryHistory radiusRead ∧
                                  UnaryHistory dyadicIntervalRead ∧ UnaryHistory locatorRead ∧
                                    UnaryHistory modulusRead ∧ UnaryHistory bracketRead ∧
                                      Cont L U endpointRead ∧
                                        Cont endpointRead rho radiusRead ∧
                                          Cont radiusRead Delta dyadicIntervalRead ∧
                                            Cont dyadicIntervalRead Lambda locatorRead ∧
                                              Cont locatorRead M modulusRead ∧
                                                Cont modulusRead bracket bracketRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryL unaryU unaryRho unaryDelta unaryLambda unaryM unaryBracket endpointRoute
    radiusRoute dyadicIntervalRoute locatorRoute modulusRoute bracketRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed endpointUnary unaryRho radiusRoute
  have dyadicIntervalUnary : UnaryHistory dyadicIntervalRead :=
    unary_cont_closed radiusUnary unaryDelta dyadicIntervalRoute
  have locatorUnary : UnaryHistory locatorRead :=
    unary_cont_closed dyadicIntervalUnary unaryLambda locatorRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed locatorUnary unaryM modulusRoute
  have bracketReadUnary : UnaryHistory bracketRead :=
    unary_cont_closed modulusUnary unaryBracket bracketRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpointRead ∨ hsame row radiusRead ∨ hsame row dyadicIntervalRead ∨
              hsame row locatorRead ∨ hsame row modulusRead ∨ hsame row bracketRead)
          (fun row : BHist => hsame row bracketRead ∧ Cont modulusRead bracket bracketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bracketRead
        ⟨hsame_refl bracketRead, bracketReadUnary⟩
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
      exact ⟨source.left, bracketRoute⟩
  }
  exact
    ⟨cert, endpointUnary, radiusUnary, dyadicIntervalUnary, locatorUnary, modulusUnary,
      bracketReadUnary, endpointRoute, radiusRoute, dyadicIntervalRoute, locatorRoute,
      modulusRoute, bracketRoute⟩

end BEDC.Derived.LocatedRealIntervalUp
