import BEDC.Derived.NatUp
import BEDC.FKernel.ExternalBinary

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def NatAdd (m n s : BHist) : Prop :=
  UnaryHistory m ∧ UnaryHistory n ∧ Cont m n s

theorem NatAdd_left_unary {m n s : BHist} :
    NatAdd m n s -> UnaryHistory m := by
  intro add
  exact add.left

theorem NatAdd_right_unary {m n s : BHist} :
    NatAdd m n s -> UnaryHistory n := by
  intro add
  exact add.right.left

theorem NatAdd_result_unary {m n s : BHist} :
    NatAdd m n s -> UnaryHistory s := by
  intro add
  exact unary_cont_closed add.left add.right.left add.right.right

theorem NatAdd_append_self {m n : BHist} :
    UnaryHistory m -> UnaryHistory n -> NatAdd m n (append m n) := by
  intro mUnary nUnary
  exact And.intro mUnary (And.intro nUnary (cont_intro rfl))

theorem NatAdd_total {m n : BHist} :
    UnaryHistory m -> UnaryHistory n ->
      ∃ s : BHist, UnaryHistory s ∧ NatAdd m n s := by
  intro mUnary nUnary
  exact Exists.intro (append m n)
    (And.intro (unary_append_closed mUnary nUnary)
      (NatAdd_append_self mUnary nUnary))

theorem NatAdd_functional {m n s t : BHist} :
    NatAdd m n s -> NatAdd m n t -> hsame s t := by
  intro left right
  exact cont_deterministic left.right.right right.right.right

theorem NatAdd_comm_hsame {m n s t : BHist} :
    NatAdd m n s -> NatAdd n m t -> hsame s t := by
  intro left right
  exact unary_cont_comm left.left left.right.left left.right.right right.right.right

theorem NatAdd_assoc_hsame {a b c ab bc abc abc' : BHist} :
    NatAdd a b ab -> NatAdd b c bc -> NatAdd ab c abc ->
      NatAdd a bc abc' -> hsame abc abc' := by
  intro addAB addBC addABC addABC'
  exact unary_continuation_associativity addAB.left addAB.right.left addBC.right.left
    addAB.right.right addBC.right.right addABC.right.right addABC'.right.right

theorem NatAdd_length {m n s : BHist} :
    NatAdd m n s ->
      BEDC.FKernel.ExternalBinary.bwordLength s =
        BEDC.FKernel.ExternalBinary.bwordLength m +
          BEDC.FKernel.ExternalBinary.bwordLength n := by
  intro add
  exact (congrArg BEDC.FKernel.ExternalBinary.bwordLength add.right.right).trans
    (BEDC.FKernel.ExternalBinary.bwordLength_append m n)

theorem NatAdd_unary_standard_bridge :
    (∀ {m n : BHist}, UnaryHistory m -> UnaryHistory n ->
      ∃ s : BHist, UnaryHistory s ∧ NatAdd m n s) ∧
    (∀ {m n s t : BHist}, NatAdd m n s -> NatAdd m n t -> hsame s t) ∧
    (∀ {m n s t : BHist}, NatAdd m n s -> NatAdd n m t -> hsame s t) ∧
    (∀ {a b c ab bc abc abc' : BHist},
      NatAdd a b ab -> NatAdd b c bc -> NatAdd ab c abc ->
        NatAdd a bc abc' -> hsame abc abc') := by
  constructor
  · intro m n mUnary nUnary
    exact NatAdd_total mUnary nUnary
  · constructor
    · intro m n s t left right
      exact NatAdd_functional left right
    · constructor
      · intro m n s t left right
        exact NatAdd_comm_hsame left right
      · intro a b c ab bc abc abc' addAB addBC addABC addABC'
        exact NatAdd_assoc_hsame addAB addBC addABC addABC'

end BEDC.Derived.NatUp
