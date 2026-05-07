import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp

def WeylGroupSourceRow
    (support : ProbeBundle BHist)
    (Vector Nonzero : BHist -> Prop)
    (root word endpoint : BHist) : Prop :=
  RootSystemFiniteSupportCarrier support Vector Nonzero root ∧
    GroupSingletonCarrier word ∧ Cont root word endpoint

theorem WeylGroupSourceRow_append_closure
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root word endpoint next product : BHist} :
    WeylGroupSourceRow support Vector Nonzero root word endpoint ->
      GroupSingletonCarrier next -> Cont endpoint next product ->
        WeylGroupSourceRow support Vector Nonzero root (append word next) product ∧
          GroupSingletonCarrier (append word next) := by
  intro row nextCarrier endpointNext
  have wordNextCarrier : GroupSingletonCarrier (append word next) :=
    append_eq_empty_iff.mpr (And.intro row.right.left nextCarrier)
  have rootWordNext : Cont root (append word next) product := by
    cases row.right.right
    cases endpointNext
    exact append_assoc root word next
  exact And.intro
    (And.intro row.left (And.intro wordNextCarrier rootWordNext))
    wordNextCarrier

end BEDC.Derived.WeylGroupUp
