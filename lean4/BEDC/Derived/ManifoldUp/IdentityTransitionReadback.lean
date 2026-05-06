import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldTransitionCoherenceLedger_identity_transition_readback
    (L : ManifoldTransitionCoherenceLedger) :
    Cont L.value L.value L.selfTransition ∧
      hsame L.selfTransition (append L.value L.value) ∧
        hsame L.selfTransition BHist.Empty ∧
          UnaryHistory L.value ∧ UnaryHistory L.selfTransition := by
  have valueEmpty : hsame L.value BHist.Empty :=
    (ManifoldSingleton_chart_coverage L.chartCarrier L.domainReadback L.valueReadback).right.right.left
  have valueUnary : UnaryHistory L.value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  have selfAppend : hsame L.selfTransition (append L.value L.value) :=
    L.identityRow
  have appendEmpty : hsame (append L.value L.value) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro valueEmpty valueEmpty)
  have selfEmpty : hsame L.selfTransition BHist.Empty :=
    hsame_trans selfAppend appendEmpty
  have selfUnary : UnaryHistory L.selfTransition :=
    unary_cont_closed valueUnary valueUnary L.identityRow
  exact And.intro L.identityRow
    (And.intro selfAppend (And.intro selfEmpty (And.intro valueUnary selfUnary)))

end BEDC.Derived.ManifoldUp
