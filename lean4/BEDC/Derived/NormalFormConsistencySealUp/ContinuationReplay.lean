import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealContinuationReplay
    {T F N K X C typedFalse normalTheorem boundaryReplay : BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              Cont T F typedFalse ->
                Cont N K normalTheorem ->
                  Cont normalTheorem X boundaryReplay ->
                    Cont boundaryReplay C typedFalse ->
                      UnaryHistory typedFalse ∧ UnaryHistory normalTheorem ∧
                        UnaryHistory boundaryReplay := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary typedFalseRoute normalTheoremRoute
    boundaryRoute _continuationRoute
  have typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed tUnary fUnary typedFalseRoute
  have normalTheoremUnary : UnaryHistory normalTheorem :=
    unary_cont_closed nUnary kUnary normalTheoremRoute
  have boundaryUnary : UnaryHistory boundaryReplay :=
    unary_cont_closed normalTheoremUnary xUnary boundaryRoute
  exact ⟨typedFalseUnary, normalTheoremUnary, boundaryUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
