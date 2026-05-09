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

end BEDC.Derived.ClebschGordanUp
