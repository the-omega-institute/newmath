import BEDC.Derived.FinitePrefixAutomatonUp.Determinacy
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_deterministic_readback
    {Q q0 A T W R R' E E' H C P N acceptance acceptance' : BHist} :
    UnaryHistory q0 ->
      UnaryHistory W ->
        UnaryHistory H ->
          UnaryHistory A ->
            Cont q0 W R ->
              Cont q0 W R' ->
                Cont R H E ->
                  Cont R' H E' ->
                    Cont E A acceptance ->
                      Cont E' A acceptance' ->
                        hsame R R' ∧ hsame E E' ∧ hsame acceptance acceptance' ∧
                          UnaryHistory E ∧ UnaryHistory E' ∧ UnaryHistory acceptance ∧
                            UnaryHistory acceptance' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro q0Unary wUnary hUnary acceptingUnary runRoute runRoute' endpointRoute endpointRoute'
    acceptanceRoute acceptanceRoute'
  have runPack :
      hsame R R' ∧ UnaryHistory R ∧ UnaryHistory R' ∧ UnaryHistory E ∧
        UnaryHistory E' :=
    FinitePrefixAutomatonCarrier_prefix_run_determinacy q0Unary wUnary hUnary runRoute
      runRoute' endpointRoute endpointRoute'
  have sameEndpoint : hsame E E' :=
    cont_respects_hsame runPack.left (hsame_refl H) endpointRoute endpointRoute'
  have sameAcceptance : hsame acceptance acceptance' :=
    cont_respects_hsame sameEndpoint (hsame_refl A) acceptanceRoute acceptanceRoute'
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed runPack.right.right.right.left acceptingUnary acceptanceRoute
  have acceptanceUnary' : UnaryHistory acceptance' :=
    unary_cont_closed runPack.right.right.right.right acceptingUnary acceptanceRoute'
  exact
    ⟨runPack.left, sameEndpoint, sameAcceptance, runPack.right.right.right.left,
      runPack.right.right.right.right, acceptanceUnary, acceptanceUnary'⟩

end BEDC.Derived.FinitePrefixAutomatonUp
