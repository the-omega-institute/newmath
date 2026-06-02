import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealProvenanceExactness
    {T F N K X H C P L dependencyRead namedRead : BHist} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory P →
                Cont T F N →
                  Cont N K dependencyRead →
                    Cont dependencyRead P namedRead →
                      hsame namedRead L →
                        UnaryHistory dependencyRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _tUnary _fUnary nUnary kUnary _xUnary pUnary _closedNormalRoute
    dependencyRoute namedRoute sameNamedLocal
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed nUnary kUnary dependencyRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed dependencyUnary pUnary namedRoute
  have _localBoundaryUnary : UnaryHistory L :=
    unary_transport namedUnary sameNamedLocal
  exact ⟨dependencyUnary, namedUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
