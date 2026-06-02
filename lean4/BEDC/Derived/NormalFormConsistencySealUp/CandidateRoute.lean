import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealCandidateRoute
    {typing falseRow normalRow theoremRow boundary transport replay provenance localName
      candidateRead routeRead : BHist} :
    Cont typing normalRow candidateRead →
      Cont candidateRead theoremRow routeRead →
        UnaryHistory typing →
          UnaryHistory normalRow →
            UnaryHistory theoremRow →
              UnaryHistory candidateRead ∧ UnaryHistory routeRead ∧ hsame boundary boundary := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro candidateRoute theoremRoute typingUnary normalUnary theoremUnary
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed typingUnary normalUnary candidateRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed candidateUnary theoremUnary theoremRoute
  exact ⟨candidateUnary, routeUnary, hsame_refl boundary⟩

end BEDC.Derived.NormalFormConsistencySealUp
