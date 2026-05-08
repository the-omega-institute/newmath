import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BilinFormRootPairingSurface
    (left right scalar endpoint ledger : BHist) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scalar ∧
    Cont left right endpoint ∧ Cont endpoint scalar ledger

theorem BilinFormRootPairingSurface_ledger_exactness_boundary
    {left right scalar endpoint ledger : BHist} :
    BilinFormRootPairingSurface left right scalar endpoint ledger ->
      UnaryHistory endpoint ∧ UnaryHistory ledger ∧ hsame endpoint (append left right) ∧
        hsame ledger (append (append left right) scalar) ∧ Cont left right endpoint ∧
          Cont endpoint scalar ledger := by
  intro surface
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointUnary surface.right.right.left surface.right.right.right.right
  have ledgerReadback : hsame ledger (append (append left right) scalar) :=
    hsame_trans surface.right.right.right.right
      (congrArg (fun h : BHist => append h scalar) surface.right.right.right.left)
  exact And.intro endpointUnary
    (And.intro ledgerUnary
      (And.intro surface.right.right.right.left
        (And.intro ledgerReadback
          (And.intro surface.right.right.right.left surface.right.right.right.right))))

end BEDC.Derived.BilinFormUp
