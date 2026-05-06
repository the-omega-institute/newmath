import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComputableUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComputableBoundedSim (P n B m : BHist) : Prop :=
  UnaryHistory P ∧ UnaryHistory n ∧ UnaryHistory B ∧ UnaryHistory m ∧ Cont n B m

def ComputableUnaryIdentityGraph (n m : BHist) : Prop :=
  UnaryHistory n ∧ UnaryHistory m ∧ hsame n m

structure ComputableBoundedGraphCertificate where
  Graph : BHist -> BHist -> Prop
  program : BHist
  bound : BHist -> BHist
  program_unary : UnaryHistory program
  bound_unary : forall {n : BHist}, UnaryHistory n -> UnaryHistory (bound n)
  graph_to_sim :
    forall {n m : BHist}, Graph n m -> ComputableBoundedSim program n (bound n) m
  sim_to_graph :
    forall {n m : BHist}, ComputableBoundedSim program n (bound n) m -> Graph n m

theorem ComputableBoundedSim_same_bound_output_hsame {P n B m mPrime : BHist} :
    ComputableBoundedSim P n B m -> ComputableBoundedSim P n B mPrime ->
      hsame m mPrime ∧ Cont n B m ∧ Cont n B mPrime := by
  intro leftRun rightRun
  exact And.intro
    (cont_deterministic leftRun.right.right.right.right rightRun.right.right.right.right)
    (And.intro leftRun.right.right.right.right rightRun.right.right.right.right)

theorem ComputableBoundedGraphCertificate_single_valuedness
    (C : ComputableBoundedGraphCertificate) {n m mPrime : BHist} :
    C.Graph n m -> C.Graph n mPrime ->
      ComputableBoundedSim C.program n (C.bound n) m ∧
        ComputableBoundedSim C.program n (C.bound n) mPrime ∧
          hsame m mPrime ∧ Cont n (C.bound n) m ∧ Cont n (C.bound n) mPrime := by
  intro leftGraph rightGraph
  have leftRun := C.graph_to_sim leftGraph
  have rightRun := C.graph_to_sim rightGraph
  have readback := ComputableBoundedSim_same_bound_output_hsame leftRun rightRun
  exact And.intro leftRun (And.intro rightRun readback)

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

theorem ComputableUnaryIdentityGraph_empty_bound_simulation_iff {n m : BHist} :
    ComputableBoundedSim BHist.Empty n BHist.Empty m <->
      (UnaryHistory n ∧ UnaryHistory m ∧ hsame n m) := by
  constructor
  · intro sim
    have sameMN : hsame m n :=
      cont_right_unit_result sim.right.right.right.right
    exact And.intro sim.right.left
      (And.intro sim.right.right.right.left (hsame_symm sameMN))
  · intro graph
    exact And.intro unary_empty
      (And.intro graph.left
        (And.intro unary_empty
          (And.intro graph.right.left
            (cont_result_hsame_transport (cont_right_unit n) graph.right.right))))

theorem ComputableUnaryIdentityGraph_empty_bound_exactness {n m : BHist} :
    ComputableBoundedSim BHist.Empty n BHist.Empty m ↔
      UnaryHistory n ∧ UnaryHistory m ∧ hsame n m := by
  constructor
  · intro sim
    have sameMN : hsame m n :=
      cont_right_unit_result sim.right.right.right.right
    exact And.intro sim.right.left
      (And.intro sim.right.right.right.left (hsame_symm sameMN))
  · intro graph
    exact And.intro unary_empty
      (And.intro graph.left
        (And.intro unary_empty
          (And.intro graph.right.left
            (cont_result_hsame_transport (cont_right_unit n) graph.right.right))))

theorem ComputableUnaryIdentityGraph_empty_bound_certificate :
    exists C : ComputableBoundedGraphCertificate,
      C.Graph = (fun n m : BHist => UnaryHistory n ∧ UnaryHistory m ∧ hsame n m) ∧
        C.program = BHist.Empty ∧
          (forall {n m : BHist}, C.Graph n m ->
            ComputableBoundedSim C.program n (C.bound n) m) ∧
            (forall {n m : BHist}, ComputableBoundedSim C.program n (C.bound n) m ->
              C.Graph n m) := by
  let C : ComputableBoundedGraphCertificate := {
    Graph := fun n m : BHist => UnaryHistory n ∧ UnaryHistory m ∧ hsame n m
    program := BHist.Empty
    bound := fun _n : BHist => BHist.Empty
    program_unary := unary_empty
    bound_unary := by
      intro _n _unaryN
      exact unary_empty
    graph_to_sim := by
      intro n m graph
      have sameNM : hsame n m := graph.right.right
      exact And.intro unary_empty
        (And.intro graph.left
          (And.intro unary_empty
            (And.intro graph.right.left
              (cont_result_hsame_transport (cont_right_unit n) sameNM))))
    sim_to_graph := by
      intro n m sim
      have sameMN : hsame m n :=
        cont_right_unit_result sim.right.right.right.right
      exact And.intro sim.right.left
        (And.intro sim.right.right.right.left (hsame_symm sameMN))
  }
  exact Exists.intro C
    (And.intro rfl
      (And.intro rfl
        (And.intro
          (by
            intro n m graph
            exact C.graph_to_sim graph)
          (by
            intro n m sim
            exact C.sim_to_graph sim))))

theorem ComputableUnaryIdentityGraph_empty_bound_simulation_exactness {n m : BHist} :
    ComputableBoundedSim BHist.Empty n BHist.Empty m <->
      (UnaryHistory n ∧ UnaryHistory m ∧ hsame n m) := by
  constructor
  · intro sim
    have sameMN : hsame m n :=
      cont_right_unit_result sim.right.right.right.right
    exact And.intro sim.right.left
      (And.intro sim.right.right.right.left (hsame_symm sameMN))
  · intro graph
    have sameNM : hsame n m := graph.right.right
    exact And.intro unary_empty
      (And.intro graph.left
        (And.intro unary_empty
          (And.intro graph.right.left
            (cont_result_hsame_transport (cont_right_unit n) sameNM))))

end BEDC.Derived.ComputableUp
