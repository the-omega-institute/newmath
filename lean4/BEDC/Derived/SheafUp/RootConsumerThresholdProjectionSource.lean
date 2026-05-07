import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootConsumerThresholdProjection_source
    (root ringed scheme pullback ledger : BHist) : Prop :=
  SheafConsumerAccessTrace root [ringed, scheme, pullback] ∧ UnaryHistory ledger ∧
    Cont root ledger pullback

theorem SheafRootConsumerThresholdProjection_source_rows
    {root ringed scheme pullback ledger : BHist} :
    SheafRootConsumerThresholdProjection_source root ringed scheme pullback ledger ->
      UnaryHistory root ∧ UnaryHistory ringed ∧ UnaryHistory scheme ∧
        UnaryHistory pullback ∧ UnaryHistory ledger ∧ Cont root ledger pullback := by
  intro source
  have ringedRow : UnaryHistory ringed :=
    source.left.right ringed (List.Mem.head [scheme, pullback])
  have schemeRow : UnaryHistory scheme :=
    source.left.right scheme (List.Mem.tail ringed (List.Mem.head [pullback]))
  have pullbackRow : UnaryHistory pullback :=
    source.left.right pullback
      (List.Mem.tail ringed (List.Mem.tail scheme (List.Mem.head [])))
  exact And.intro source.left.left
    (And.intro ringedRow
      (And.intro schemeRow
        (And.intro pullbackRow
          (And.intro source.right.left source.right.right))))

end BEDC.Derived.SheafUp
