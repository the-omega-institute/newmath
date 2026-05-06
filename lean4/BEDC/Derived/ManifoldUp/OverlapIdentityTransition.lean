import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldSingleton_overlap_identity_transition
    (row : ManifoldTransitionCoherenceLedger) :
    ManifoldSingletonCarrier row.chart ∧
      hsame row.selfTransition (append row.value row.value) ∧
        Cont row.value row.value row.selfTransition ∧
          UnaryHistory row.value ∧ UnaryHistory row.selfTransition := by
  have rows :=
    ManifoldSingleton_chart_coverage row.chartCarrier row.domainReadback row.valueReadback
  have valueUnary : UnaryHistory row.value := rows.right.right.right
  have selfUnary : UnaryHistory row.selfTransition :=
    unary_cont_closed valueUnary valueUnary row.identityRow
  exact And.intro row.chartCarrier
    (And.intro row.identityRow
      (And.intro row.identityRow (And.intro valueUnary selfUnary)))

end BEDC.Derived.ManifoldUp
