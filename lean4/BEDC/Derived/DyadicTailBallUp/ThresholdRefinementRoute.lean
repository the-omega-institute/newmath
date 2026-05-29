import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicTailBallThresholdRefinementRoute
    {D F Dref Fref B R oldRead newRead terminalRead : BHist} :
    UnaryHistory Dref →
      UnaryHistory Fref →
        UnaryHistory R →
          Cont D F oldRead →
            Cont Dref Fref newRead →
              hsame oldRead newRead →
                hsame newRead B →
                  Cont B R terminalRead →
                    UnaryHistory oldRead ∧ UnaryHistory newRead ∧
                      UnaryHistory terminalRead ∧ Cont Dref Fref oldRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro drefUnary frefUnary rUnary oldRoute refinedRoute sameOldNew sameNewBall terminalRoute
  have newUnary : UnaryHistory newRead :=
    unary_cont_closed drefUnary frefUnary refinedRoute
  have oldUnary : UnaryHistory oldRead :=
    unary_transport_symm newUnary sameOldNew
  have ballUnary : UnaryHistory B :=
    unary_transport newUnary sameNewBall
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed ballUnary rUnary terminalRoute
  have oldRefinedRoute : Cont Dref Fref oldRead :=
    cont_result_hsame_transport refinedRoute (hsame_symm sameOldNew)
  exact ⟨oldUnary, newUnary, terminalUnary, oldRefinedRoute⟩

end BEDC.Derived.DyadicTailBallUp
