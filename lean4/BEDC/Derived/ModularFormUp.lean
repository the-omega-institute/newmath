import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ModularFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ModularFormQExpansionCarrier
    (holomorphic automorphic coefficient transform provenance ledger : BHist) : Prop :=
  UnaryHistory holomorphic ∧
    UnaryHistory automorphic ∧
      UnaryHistory coefficient ∧
        UnaryHistory transform ∧
          Cont holomorphic coefficient provenance ∧
            Cont automorphic transform ledger ∧ Cont provenance transform ledger

theorem ModularFormQExpansionCarrier_holomorphic_source_scope
    {holomorphic automorphic coefficient transform provenance ledger : BHist} :
    ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance ledger ->
      UnaryHistory holomorphic ∧
        UnaryHistory automorphic ∧
          UnaryHistory coefficient ∧
            Cont holomorphic coefficient provenance ∧ Cont automorphic transform ledger := by
  intro carrier
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.right.left
            carrier.right.right.right.right.right.left)))

end BEDC.Derived.ModularFormUp
