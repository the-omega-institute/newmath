import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_even_product_classifier_obligation [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger product'
      boundary' cliffordEndpoint' groupWord' spinEndpoint' : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame product product' ->
        hsame boundary boundary' ->
          hsame groupWord groupWord' ->
            Cont product' boundary' cliffordEndpoint' ->
              Cont cliffordEndpoint' groupWord' spinEndpoint' ->
                SpinGroupRootCarrier unit vector product' boundary' cliffordEndpoint' groupWord'
                    spinEndpoint' ledger bundle pkg ∧
                  hsame spinEndpoint spinEndpoint' ∧ UnaryHistory product' ∧
                    UnaryHistory boundary' := by
  intro carrier sameProduct sameBoundary sameGroup cliffordRow spinRow
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.left.right.left carrier.left.right.left
      carrier.left.right.right.right.left
  have productUnary' : UnaryHistory product' :=
    unary_transport productUnary sameProduct
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_transport carrier.left.right.right.left sameBoundary
  have productRow' : Cont vector vector product' :=
    cont_result_hsame_transport carrier.left.right.right.right.left sameProduct
  have cliffordSame : hsame cliffordEndpoint cliffordEndpoint' :=
    cont_respects_hsame sameProduct sameBoundary carrier.left.right.right.right.right
      cliffordRow
  have clifford' : CliffordCarrierPackage unit vector product' boundary' cliffordEndpoint' :=
    And.intro carrier.left.left
      (And.intro carrier.left.right.left
        (And.intro boundaryUnary'
          (And.intro productRow' cliffordRow)))
  have group' : GroupSingletonCarrier groupWord' :=
    hsame_trans (hsame_symm sameGroup) carrier.right.left
  have sameSpin : hsame spinEndpoint spinEndpoint' :=
    cont_respects_hsame cliffordSame sameGroup carrier.right.right.left spinRow
  exact
    And.intro
      (And.intro clifford'
        (And.intro group'
          (And.intro spinRow carrier.right.right.right)))
      (And.intro sameSpin (And.intro productUnary' boundaryUnary'))

end BEDC.Derived.SpinGroupUp
