import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClebschGordanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClebschGordanCouplingPacket [AskSetup] [PackageSetup]
    (lie tensor repr sourceLeft sourceRight tensorEndpoint decomposition coefficients classifier
      provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lie ∧ UnaryHistory tensor ∧ UnaryHistory repr ∧ UnaryHistory sourceLeft ∧
    UnaryHistory sourceRight ∧ UnaryHistory decomposition ∧ UnaryHistory classifier ∧
      Cont sourceLeft sourceRight tensorEndpoint ∧
        Cont tensorEndpoint decomposition coefficients ∧ Cont coefficients classifier ledger ∧
          PkgSig bundle provenance pkg

theorem ClebschGordanCouplingPacket_carrier_source_obligation [AskSetup] [PackageSetup]
    {lie tensor repr sourceLeft sourceRight tensorEndpoint decomposition coefficients classifier
      provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClebschGordanCouplingPacket lie tensor repr sourceLeft sourceRight tensorEndpoint
        decomposition coefficients classifier provenance ledger bundle pkg ->
      UnaryHistory sourceLeft -> UnaryHistory sourceRight -> UnaryHistory decomposition ->
        UnaryHistory classifier ->
          UnaryHistory tensorEndpoint ∧ UnaryHistory coefficients ∧ UnaryHistory ledger ∧
            Cont sourceLeft sourceRight tensorEndpoint ∧
              Cont tensorEndpoint decomposition coefficients ∧
                Cont coefficients classifier ledger ∧ PkgSig bundle provenance pkg := by
  intro packet sourceLeftUnary sourceRightUnary decompositionUnary classifierUnary
  have tensorEndpointRow : Cont sourceLeft sourceRight tensorEndpoint :=
    packet.right.right.right.right.right.right.right.left
  have coefficientRow : Cont tensorEndpoint decomposition coefficients :=
    packet.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont coefficients classifier ledger :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgRow : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  have tensorEndpointUnary : UnaryHistory tensorEndpoint :=
    unary_cont_closed sourceLeftUnary sourceRightUnary tensorEndpointRow
  have coefficientsUnary : UnaryHistory coefficients :=
    unary_cont_closed tensorEndpointUnary decompositionUnary coefficientRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed coefficientsUnary classifierUnary ledgerRow
  exact And.intro tensorEndpointUnary
    (And.intro coefficientsUnary
      (And.intro ledgerUnary
        (And.intro tensorEndpointRow
          (And.intro coefficientRow
            (And.intro ledgerRow pkgRow)))))

theorem ClebschGordanCouplingPacket_classifier_transport_obligation [AskSetup] [PackageSetup]
    {lie tensor repr sourceLeft sourceRight tensorEndpoint decomposition coefficients classifier
      provenance ledger lie' tensor' repr' sourceLeft' sourceRight' tensorEndpoint'
      decomposition' coefficients' classifier' provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClebschGordanCouplingPacket lie tensor repr sourceLeft sourceRight tensorEndpoint
        decomposition coefficients classifier provenance ledger bundle pkg ->
      hsame lie lie' -> hsame tensor tensor' -> hsame repr repr' ->
        hsame sourceLeft sourceLeft' -> hsame sourceRight sourceRight' ->
          hsame decomposition decomposition' -> hsame classifier classifier' ->
            Cont sourceLeft' sourceRight' tensorEndpoint' ->
              Cont tensorEndpoint' decomposition' coefficients' ->
                Cont coefficients' classifier' ledger' -> PkgSig bundle provenance' pkg ->
                  hsame tensorEndpoint tensorEndpoint' ∧ hsame coefficients coefficients' ∧
                    hsame ledger ledger' ∧
                      ClebschGordanCouplingPacket lie' tensor' repr' sourceLeft' sourceRight'
                        tensorEndpoint' decomposition' coefficients' classifier' provenance'
                        ledger' bundle pkg := by
  intro packet sameLie sameTensor sameRepr sameSourceLeft sameSourceRight sameDecomposition
    sameClassifier tensorEndpointRow' coefficientRow' ledgerRow' pkgRow'
  have lieUnary : UnaryHistory lie :=
    packet.left
  have tensorUnary : UnaryHistory tensor :=
    packet.right.left
  have reprUnary : UnaryHistory repr :=
    packet.right.right.left
  have sourceLeftUnary : UnaryHistory sourceLeft :=
    packet.right.right.right.left
  have sourceRightUnary : UnaryHistory sourceRight :=
    packet.right.right.right.right.left
  have decompositionUnary : UnaryHistory decomposition :=
    packet.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    packet.right.right.right.right.right.right.left
  have tensorEndpointRow : Cont sourceLeft sourceRight tensorEndpoint :=
    packet.right.right.right.right.right.right.right.left
  have coefficientRow : Cont tensorEndpoint decomposition coefficients :=
    packet.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont coefficients classifier ledger :=
    packet.right.right.right.right.right.right.right.right.right.left
  have lieUnary' : UnaryHistory lie' :=
    unary_transport lieUnary sameLie
  have tensorUnary' : UnaryHistory tensor' :=
    unary_transport tensorUnary sameTensor
  have reprUnary' : UnaryHistory repr' :=
    unary_transport reprUnary sameRepr
  have sourceLeftUnary' : UnaryHistory sourceLeft' :=
    unary_transport sourceLeftUnary sameSourceLeft
  have sourceRightUnary' : UnaryHistory sourceRight' :=
    unary_transport sourceRightUnary sameSourceRight
  have decompositionUnary' : UnaryHistory decomposition' :=
    unary_transport decompositionUnary sameDecomposition
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have sameTensorEndpoint : hsame tensorEndpoint tensorEndpoint' :=
    cont_respects_hsame sameSourceLeft sameSourceRight tensorEndpointRow tensorEndpointRow'
  have sameCoefficients : hsame coefficients coefficients' :=
    cont_respects_hsame sameTensorEndpoint sameDecomposition coefficientRow coefficientRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameCoefficients sameClassifier ledgerRow ledgerRow'
  have tensorEndpointUnary' : UnaryHistory tensorEndpoint' :=
    unary_cont_closed sourceLeftUnary' sourceRightUnary' tensorEndpointRow'
  have coefficientsUnary' : UnaryHistory coefficients' :=
    unary_cont_closed tensorEndpointUnary' decompositionUnary' coefficientRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed coefficientsUnary' classifierUnary' ledgerRow'
  have targetPacket :
      ClebschGordanCouplingPacket lie' tensor' repr' sourceLeft' sourceRight'
        tensorEndpoint' decomposition' coefficients' classifier' provenance' ledger' bundle pkg :=
    And.intro lieUnary'
      (And.intro tensorUnary'
        (And.intro reprUnary'
          (And.intro sourceLeftUnary'
            (And.intro sourceRightUnary'
              (And.intro decompositionUnary'
                (And.intro classifierUnary'
                  (And.intro tensorEndpointRow'
                    (And.intro coefficientRow'
                      (And.intro ledgerRow' pkgRow')))))))))
  exact And.intro sameTensorEndpoint
    (And.intro sameCoefficients
      (And.intro sameLedger targetPacket))

end BEDC.Derived.ClebschGordanUp
