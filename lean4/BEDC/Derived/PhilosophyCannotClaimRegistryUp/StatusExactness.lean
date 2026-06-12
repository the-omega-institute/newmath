import BEDC.Derived.PhilosophyCannotClaimRegistryUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhilosophyCannotClaimRegistryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PhilosophyCannotClaimRegistryStatusExactness
    {C S E U B H K P N statusRead blockRead refusalRead : BHist} :
    Cont S B refusalRead ->
      Cont S E statusRead ->
        Cont B U blockRead ->
          UnaryHistory S ->
            UnaryHistory B ->
              UnaryHistory E ->
                UnaryHistory U ->
                  UnaryHistory refusalRead ∧
                    UnaryHistory statusRead ∧
                      UnaryHistory blockRead ∧
                        philosophyCannotClaimRegistryFields
                            (PhilosophyCannotClaimRegistryUp.mk C S E U B H K P N) =
                          [C, S, E, U, B, H, K, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro refusalRoute statusRoute blockRoute statusUnary blockUnary exclusionUnary upgradeUnary
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed statusUnary blockUnary refusalRoute
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed statusUnary exclusionUnary statusRoute
  have blockReadUnary : UnaryHistory blockRead :=
    unary_cont_closed blockUnary upgradeUnary blockRoute
  exact ⟨refusalUnary, statusReadUnary, blockReadUnary, rfl⟩

end BEDC.Derived.PhilosophyCannotClaimRegistryUp
