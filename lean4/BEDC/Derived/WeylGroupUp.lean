import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp

def WeylGroupBHistSourceRow
    (support : ProbeBundle BHist) (Vector Nonzero : BHist -> Prop)
    (root word action : BHist) : Prop :=
  RootSystemFiniteSupportCarrier support Vector Nonzero root ∧
    GroupSingletonCarrier word ∧ Cont root word action ∧ UnaryHistory action

theorem WeylGroupBHistSourceRow_simple_reflection_word_closure
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root wordA wordB actionA actionAB : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root wordA actionA ->
      GroupSingletonCarrier wordB -> Cont actionA wordB actionAB ->
        WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB) actionAB ∧
          hsame actionAB root ∧ GroupSingletonCarrier (append wordA wordB) := by
  intro source wordBCarrier actionStep
  have rootUnary : UnaryHistory root :=
    vector_unary source.left.right.left
  have wordAEmpty : hsame wordA BHist.Empty := source.right.left
  have wordBEmpty : hsame wordB BHist.Empty := wordBCarrier
  have wordAppendCarrier : GroupSingletonCarrier (append wordA wordB) :=
    append_eq_empty_iff.mpr (And.intro wordAEmpty wordBEmpty)
  have actionSameRoot : hsame actionA root :=
    cont_right_unit_result (by
      cases wordAEmpty
      exact source.right.right.left)
  have actionABSameActionA : hsame actionAB actionA :=
    cont_right_unit_result (by
      cases wordBEmpty
      exact actionStep)
  have actionABSameRoot : hsame actionAB root :=
    hsame_trans actionABSameActionA actionSameRoot
  have composedRow : Cont root (append wordA wordB) actionAB := by
    cases source.right.right.left
    cases actionStep
    exact append_assoc root wordA wordB
  have actionABUnary : UnaryHistory actionAB :=
    unary_transport rootUnary (hsame_symm actionABSameRoot)
  exact And.intro
    (And.intro source.left
      (And.intro wordAppendCarrier (And.intro composedRow actionABUnary)))
    (And.intro actionABSameRoot wordAppendCarrier)

end BEDC.Derived.WeylGroupUp
