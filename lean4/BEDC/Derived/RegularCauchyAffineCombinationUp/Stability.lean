import BEDC.Derived.RegularCauchyAffineCombinationUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyAffineCombinationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyAffineCombinationCarrier_stability
    {q x y wx wy dq dbarq sx sy sum e r z h c p n qRead xRead yRead sxRead syRead
      sumRead ledgerRead : BHist} :
    UnaryHistory q ->
      UnaryHistory x ->
        UnaryHistory y ->
          UnaryHistory wx ->
            UnaryHistory wy ->
              UnaryHistory dq ->
                UnaryHistory dbarq ->
                  UnaryHistory sx ->
                    UnaryHistory sy ->
                      UnaryHistory sum ->
                        UnaryHistory e ->
                          Cont q dq qRead ->
                            Cont x wx xRead ->
                              Cont y wy yRead ->
                                Cont qRead xRead sxRead ->
                                  Cont yRead dbarq syRead ->
                                    Cont sxRead syRead sumRead ->
                                      Cont sumRead e ledgerRead ->
                                      regularCauchyAffineCombinationFields
                                          (RegularCauchyAffineCombinationUp.mk
                                            q x y wx wy dq dbarq sx sy sum e r z h c p n) =
                                        [q, x, y, wx, wy, dq, dbarq, sx, sy, sum, e, r,
                                          z, h, c, p, n] ∧
                                        UnaryHistory qRead ∧ UnaryHistory xRead ∧
                                          UnaryHistory yRead ∧ UnaryHistory sxRead ∧
                                            UnaryHistory syRead ∧ UnaryHistory sumRead ∧
                                              UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro coefficientUnary leftUnary rightUnary leftWindowUnary rightWindowUnary dyadicUnary
    complementUnary scaleLeftUnary scaleRightUnary sumUnary ledgerUnary coefficientRoute leftRoute
    rightRoute scaleLeftRoute scaleRightRoute sumRoute ledgerRoute
  have qReadUnary : UnaryHistory qRead :=
    unary_cont_closed coefficientUnary dyadicUnary coefficientRoute
  have xReadUnary : UnaryHistory xRead :=
    unary_cont_closed leftUnary leftWindowUnary leftRoute
  have yReadUnary : UnaryHistory yRead :=
    unary_cont_closed rightUnary rightWindowUnary rightRoute
  have sxReadUnary : UnaryHistory sxRead :=
    unary_cont_closed qReadUnary xReadUnary scaleLeftRoute
  have syReadUnary : UnaryHistory syRead :=
    unary_cont_closed yReadUnary complementUnary scaleRightRoute
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed sxReadUnary syReadUnary sumRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sumReadUnary ledgerUnary ledgerRoute
  exact
    ⟨rfl, qReadUnary, xReadUnary, yReadUnary, sxReadUnary, syReadUnary, sumReadUnary,
      ledgerReadUnary⟩

end BEDC.Derived.RegularCauchyAffineCombinationUp
