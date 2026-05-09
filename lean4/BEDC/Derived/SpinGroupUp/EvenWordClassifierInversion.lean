import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_even_word_classifier_inversion [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger classifierRow
      evenWord fiberRow : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont product groupWord evenWord ->
        Cont spinEndpoint BHist.Empty fiberRow ->
          hsame classifierRow spinEndpoint ->
            UnaryHistory evenWord ∧ UnaryHistory fiberRow ∧
              hsame evenWord (append product groupWord) ∧ hsame fiberRow spinEndpoint ∧
                GroupSingletonCarrier groupWord ∧ PkgSig bundle ledger pkg := by
  intro carrier evenWordRow fiberRowRow _classifierRowSame
  have scope := SpinGroupRootCarrier_source_scope carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.left.right.left carrier.left.right.left
      carrier.left.right.right.right.left
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm scope.right.left)
  have evenWordUnary : UnaryHistory evenWord :=
    unary_cont_closed productUnary groupUnary evenWordRow
  have fiberRowUnary : UnaryHistory fiberRow :=
    unary_cont_closed scope.right.right.left unary_empty fiberRowRow
  have fiberSame : hsame fiberRow spinEndpoint :=
    cont_right_unit_result fiberRowRow
  exact
    And.intro evenWordUnary
      (And.intro fiberRowUnary
        (And.intro evenWordRow
          (And.intro fiberSame
            (And.intro scope.right.left scope.right.right.right.right))))

end BEDC.Derived.SpinGroupUp
