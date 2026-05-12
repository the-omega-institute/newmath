import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FastSeriesProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastSeriesProductCarrier [AskSetup] [PackageSetup]
    (f g k w m t r e l c p n endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory k ∧ UnaryHistory w ∧
    UnaryHistory m ∧ UnaryHistory t ∧ UnaryHistory r ∧ UnaryHistory e ∧
      UnaryHistory l ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
        UnaryHistory endpoint ∧ Cont f g k ∧ Cont k w m ∧ Cont m t r ∧
          Cont r e endpoint ∧ PkgSig bundle endpoint pkg

theorem FastSeriesProductCarrier_tail_bound_convolution [AskSetup] [PackageSetup]
    {f g k w m t r e l c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastSeriesProductCarrier f g k w m t r e l c p n endpoint bundle pkg ->
      UnaryHistory k ∧ UnaryHistory w ∧ UnaryHistory m ∧ UnaryHistory t ∧
        Cont k w m ∧ Cont m t r ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.FastSeriesProductUp
