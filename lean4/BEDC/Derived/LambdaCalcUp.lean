import BEDC.Derived.TreeUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

def LambdaCalcBHistTermCarrier (h : BHist) : Prop :=
  ∃ tag index connected acyclic root endpoint : BHist,
    UnaryHistory index ∧ TreeBHistCarrier tag index connected acyclic root endpoint ∧
      hsame h (append (BHist.e1 BHist.Empty) index)

theorem LambdaCalcBHistTermCarrier_variable_constructor_carrier
    {i h tag endpoint connected acyclic root : BHist} :
    UnaryHistory i -> TreeBHistCarrier tag i connected acyclic root endpoint ->
      hsame h (append (BHist.e1 BHist.Empty) i) ->
        LambdaCalcBHistTermCarrier h ∧ UnaryHistory i := by
  intro indexUnary treeCarrier visibleEndpoint
  have rows := TreeBHistCarrier_exactness_rows treeCarrier
  have transportedVisible : hsame h (append (BHist.e1 BHist.Empty) i) :=
    hsame_trans visibleEndpoint (hsame_refl (append (BHist.e1 BHist.Empty) i))
  have termCarrier : LambdaCalcBHistTermCarrier h :=
    Exists.intro tag
      (Exists.intro i
        (Exists.intro connected
          (Exists.intro acyclic
            (Exists.intro root
              (Exists.intro endpoint
                (And.intro indexUnary (And.intro treeCarrier transportedVisible)))))))
  exact And.intro termCarrier rows.left.right.left

end BEDC.Derived.LambdaCalcUp
