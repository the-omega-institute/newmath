import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComputableUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComputableBoundedSim (P n B m : BHist) : Prop :=
  UnaryHistory P ∧ UnaryHistory n ∧ UnaryHistory B ∧ UnaryHistory m ∧ Cont n B m

theorem ComputableBoundedSim_same_bound_output_deterministic {P n B m m' : BHist} :
    ComputableBoundedSim P n B m -> ComputableBoundedSim P n B m' ->
      hsame m m' ∧ UnaryHistory m ∧ UnaryHistory m' := by
  intro leftRun rightRun
  exact And.intro
    (cont_deterministic leftRun.right.right.right.right rightRun.right.right.right.right)
    (And.intro leftRun.right.right.right.left rightRun.right.right.right.left)

theorem ComputableBoundedSim_composition {PF PG n bF m bG k : BHist} :
    ComputableBoundedSim PF n bF m -> ComputableBoundedSim PG m bG k ->
      exists B : BHist, UnaryHistory B ∧ Cont bF bG B ∧
        ComputableBoundedSim (append PF PG) n B k := by
  intro leftRun rightRun
  refine Exists.intro (append bF bG) ?_
  have programUnary : UnaryHistory (append PF PG) :=
    unary_append_closed leftRun.left rightRun.left
  have boundUnary : UnaryHistory (append bF bG) :=
    unary_append_closed leftRun.right.right.left rightRun.right.right.left
  have composedCont : Cont n (append bF bG) k := by
    cases leftRun.right.right.right.right
    cases rightRun.right.right.right.right
    exact append_assoc n bF bG
  exact And.intro boundUnary
    (And.intro (cont_intro rfl)
      (And.intro programUnary
        (And.intro leftRun.right.left
          (And.intro boundUnary
            (And.intro rightRun.right.right.right.left composedCont)))))

end BEDC.Derived.ComputableUp
