import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont

theorem ManifoldTransitionCoherenceLedger_exhaustion
    (row : ManifoldTransitionCoherenceLedger) :
    Cont row.value row.value row.selfTransition ∧
      Cont row.selfTransition row.selfTransition row.inverseRound ∧
        Cont row.inverseRound row.value row.cocycle := by
  exact And.intro row.identityRow (And.intro row.inverseRoundRow row.cocycleRow)

end BEDC.Derived.ManifoldUp
