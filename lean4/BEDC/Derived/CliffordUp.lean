import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CliffordUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CliffordCarrierPackage_product_stability_obligation
    {left left' right right' product product' : BHist} :
    UnaryHistory left -> UnaryHistory right ->
      hsame left left' -> hsame right right' ->
        Cont left right product -> Cont left' right' product' ->
          UnaryHistory product ∧ UnaryHistory product' ∧ hsame product product' := by
  intro leftCarrier rightCarrier sameLeft sameRight productCont productCont'
  have productCarrier : UnaryHistory product :=
    unary_cont_closed leftCarrier rightCarrier productCont
  have leftCarrier' : UnaryHistory left' :=
    unary_transport leftCarrier sameLeft
  have rightCarrier' : UnaryHistory right' :=
    unary_transport rightCarrier sameRight
  have productCarrier' : UnaryHistory product' :=
    unary_cont_closed leftCarrier' rightCarrier' productCont'
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameLeft sameRight productCont productCont'
  exact And.intro productCarrier (And.intro productCarrier' sameProduct)

def CliffordCarrierPackage (unit vector product boundary endpoint : BHist) : Prop :=
  UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory boundary ∧
    Cont vector vector product ∧ Cont product boundary endpoint

def CliffordClassifierPackage
    (unit vector product boundary endpoint scalar scalarUnit : BHist) : Prop :=
  CliffordCarrierPackage unit vector product boundary endpoint ∧ UnaryHistory scalar ∧
    Cont scalar unit scalarUnit ∧ hsame endpoint scalarUnit

theorem CliffordCarrierPackage_product_relation_stability
    {unit vector vector' product product' boundary endpoint endpoint' : BHist} :
    CliffordCarrierPackage unit vector product boundary endpoint ->
      hsame vector vector' ->
        Cont vector' vector' product' ->
          Cont product' boundary endpoint' ->
            CliffordCarrierPackage unit vector' product' boundary endpoint' ∧
              hsame product product' ∧ hsame endpoint endpoint' := by
  intro carrier sameVector productCont endpointCont
  have vector'Unary : UnaryHistory vector' :=
    unary_transport carrier.right.left sameVector
  have productUnary : UnaryHistory product' :=
    unary_cont_closed vector'Unary vector'Unary productCont
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameVector sameVector carrier.right.right.right.left productCont
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProduct (hsame_refl boundary)
      carrier.right.right.right.right endpointCont
  constructor
  · exact
      And.intro carrier.left
        (And.intro vector'Unary
          (And.intro carrier.right.right.left
            (And.intro productCont endpointCont)))
  · exact And.intro sameProduct sameEndpoint

theorem CliffordCarrierPackage_product_relation_stability_obligations
    {unit left right leftSquare rightSquare boundary leftEndpoint rightEndpoint context
      leftProduct rightProduct : BHist} :
    CliffordCarrierPackage unit left leftSquare boundary leftEndpoint ->
      CliffordCarrierPackage unit right rightSquare boundary rightEndpoint ->
        hsame left right ->
          UnaryHistory context ->
            Cont left context leftProduct ->
              Cont right context rightProduct ->
                UnaryHistory leftProduct ∧ UnaryHistory rightProduct ∧
                  hsame leftProduct rightProduct := by
  intro leftPackage rightPackage sameLeftRight contextCarrier leftContext rightContext
  exact
    CliffordCarrierPackage_product_stability_obligation
      leftPackage.right.left contextCarrier sameLeftRight (hsame_refl context)
      leftContext rightContext

theorem CliffordCarrierPackage_ledger_exactness_obligations
    {unit vector product boundary endpoint endpoint' : BHist} :
    CliffordCarrierPackage unit vector product boundary endpoint ->
      hsame endpoint endpoint' ->
        Cont product boundary endpoint' ->
          CliffordCarrierPackage unit vector product boundary endpoint' ∧
            UnaryHistory product ∧ UnaryHistory endpoint' := by
  intro carrier sameEndpoint endpointCont
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.right.left carrier.right.left carrier.right.right.right.left
  have endpointUnarySource : UnaryHistory endpoint :=
    unary_cont_closed productUnary carrier.right.right.left carrier.right.right.right.right
  have endpointUnary : UnaryHistory endpoint' :=
    unary_transport endpointUnarySource sameEndpoint
  constructor
  · exact
      And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left endpointCont)))
  · exact And.intro productUnary endpointUnary

theorem CliffordCarrierPackage_universal_ledger_exactness
    {unit vector product boundary endpoint : BHist} :
    CliffordCarrierPackage unit vector product boundary endpoint ->
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory endpoint ∧ Cont vector vector product ∧ Cont product boundary endpoint ∧
          hsame product (append vector vector) ∧
            hsame endpoint (append (append vector vector) boundary) := by
  intro carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.right.left carrier.right.left carrier.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed productUnary carrier.right.right.left carrier.right.right.right.right
  have endpointReadback : hsame endpoint (append (append vector vector) boundary) :=
    hsame_trans carrier.right.right.right.right
      (congrArg (fun h : BHist => append h boundary) carrier.right.right.right.left)
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro productUnary
          (And.intro carrier.right.right.left
            (And.intro endpointUnary
              (And.intro carrier.right.right.right.left
                (And.intro carrier.right.right.right.right
                  (And.intro carrier.right.right.right.left endpointReadback)))))))

theorem CliffordCarrierPackage_ledger_exactness_obligation
    {unit vector product boundary endpoint : BHist} :
    CliffordCarrierPackage unit vector product boundary endpoint ->
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory endpoint ∧ Cont vector vector product ∧ Cont product boundary endpoint ∧
          hsame product (append vector vector) ∧
            hsame endpoint (append (append vector vector) boundary) :=
  CliffordCarrierPackage_universal_ledger_exactness

theorem CliffordClassifierPackage_quadratic_relation_obligation
    {unit vector product boundary endpoint scalar scalarEndpoint : BHist} :
    CliffordClassifierPackage unit vector product boundary endpoint scalar scalarEndpoint ->
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory scalar ∧ UnaryHistory scalarEndpoint ∧ Cont vector vector product ∧
          Cont product boundary endpoint ∧ Cont scalar unit scalarEndpoint ∧
            hsame endpoint scalarEndpoint := by
  intro classifier
  have carrier : CliffordCarrierPackage unit vector product boundary endpoint :=
    classifier.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.right.left carrier.right.left carrier.right.right.right.left
  have scalarEndpointUnary : UnaryHistory scalarEndpoint :=
    unary_cont_closed classifier.right.left carrier.left classifier.right.right.left
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro productUnary
          (And.intro carrier.right.right.left
            (And.intro classifier.right.left
              (And.intro scalarEndpointUnary
                (And.intro carrier.right.right.right.left
                  (And.intro carrier.right.right.right.right
                    (And.intro classifier.right.right.left classifier.right.right.right))))))))

theorem CliffordCarrierPackage_carrier_classifier_obligations
    {unit vector product boundary endpoint scalar scalarUnit : BHist} :
    CliffordClassifierPackage unit vector product boundary endpoint scalar scalarUnit ->
      CliffordCarrierPackage unit vector product boundary endpoint ∧ UnaryHistory unit ∧
        UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
          UnaryHistory endpoint ∧ UnaryHistory scalar ∧ UnaryHistory scalarUnit ∧
            Cont vector vector product ∧ Cont product boundary endpoint ∧
              Cont scalar unit scalarUnit ∧ hsame endpoint scalarUnit := by
  intro classifier
  have carrier : CliffordCarrierPackage unit vector product boundary endpoint :=
    classifier.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.right.left carrier.right.left carrier.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed productUnary carrier.right.right.left carrier.right.right.right.right
  have scalarUnitUnary : UnaryHistory scalarUnit :=
    unary_cont_closed classifier.right.left carrier.left classifier.right.right.left
  exact
    And.intro carrier
      (And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro productUnary
            (And.intro carrier.right.right.left
              (And.intro endpointUnary
                (And.intro classifier.right.left
                  (And.intro scalarUnitUnary
                    (And.intro carrier.right.right.right.left
                      (And.intro carrier.right.right.right.right
                        (And.intro classifier.right.right.left
                          classifier.right.right.right))))))))))

theorem CliffordCarrierPackage_universal_factorization_obligation
    {unit vector product boundary endpoint scalar scalarEndpoint target targetProduct
      targetEndpoint : BHist} :
    CliffordClassifierPackage unit vector product boundary endpoint scalar scalarEndpoint ->
      UnaryHistory target ->
        Cont target target targetProduct ->
          Cont targetProduct boundary targetEndpoint ->
            hsame targetEndpoint scalarEndpoint ->
              CliffordCarrierPackage unit target targetProduct boundary targetEndpoint ∧
                hsame endpoint targetEndpoint ∧ UnaryHistory targetEndpoint := by
  intro classifier targetUnary targetSquare targetBoundary sameTargetEndpoint
  have carrier : CliffordCarrierPackage unit vector product boundary endpoint :=
    classifier.left
  have targetProductUnary : UnaryHistory targetProduct :=
    unary_cont_closed targetUnary targetUnary targetSquare
  have targetEndpointUnary : UnaryHistory targetEndpoint :=
    unary_cont_closed targetProductUnary carrier.right.right.left targetBoundary
  have sameEndpointTarget : hsame endpoint targetEndpoint :=
    hsame_trans classifier.right.right.right (hsame_symm sameTargetEndpoint)
  exact
    And.intro
      (And.intro carrier.left
        (And.intro targetUnary
          (And.intro carrier.right.right.left
            (And.intro targetSquare targetBoundary))))
      (And.intro sameEndpointTarget targetEndpointUnary)

end BEDC.Derived.CliffordUp
