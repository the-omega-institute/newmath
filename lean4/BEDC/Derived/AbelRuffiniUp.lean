import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelRuffiniUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AbelRuffiniDerivedSeriesLedger_assoc_surface
    {galois sym commutator subgroup next : BHist} :
    UnaryHistory galois -> UnaryHistory sym -> UnaryHistory commutator ->
      Cont galois sym subgroup -> Cont subgroup commutator next ->
        ∃ tail : BHist, ∃ packed : BHist,
          Cont sym commutator tail ∧ Cont galois tail packed ∧ UnaryHistory subgroup ∧
            UnaryHistory tail ∧ UnaryHistory next ∧ UnaryHistory packed ∧ hsame next packed := by
  intro galoisUnary symUnary commutatorUnary subgroupRow nextRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisUnary symUnary subgroupRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  cases cont_assoc_left_exists subgroupRow nextRow with
  | intro tail repacked =>
      have tailUnary : UnaryHistory tail :=
        unary_cont_closed symUnary commutatorUnary repacked.left
      exact
        ⟨tail, next, repacked.left, repacked.right, subgroupUnary, tailUnary, nextUnary,
          nextUnary, hsame_refl next⟩

end BEDC.Derived.AbelRuffiniUp
