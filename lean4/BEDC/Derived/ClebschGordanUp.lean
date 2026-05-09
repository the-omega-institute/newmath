import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClebschGordanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ClebschGordanCouplingPacket_ledger_exactness_obligation [AskSetup] [PackageSetup]
    {lie tensor repr sourceLeft sourceRight tensorEndpoint decomposition coefficients classifier
      provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClebschGordanCouplingPacket lie tensor repr sourceLeft sourceRight tensorEndpoint
        decomposition coefficients classifier provenance ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger) (fun row : BHist => hsame row ledger)
        hsame ∧
        UnaryHistory tensorEndpoint ∧ UnaryHistory coefficients ∧ UnaryHistory ledger ∧
          Cont sourceLeft sourceRight tensorEndpoint ∧
            Cont tensorEndpoint decomposition coefficients ∧
              Cont coefficients classifier ledger ∧ PkgSig bundle provenance pkg := by
  intro packet
  have sourceLeftUnary : UnaryHistory sourceLeft :=
    packet.right.right.right.left
  have sourceRightUnary : UnaryHistory sourceRight :=
    packet.right.right.right.right.left
  have decompositionUnary : UnaryHistory decomposition :=
    packet.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    packet.right.right.right.right.right.right.left
  have rows :=
    ClebschGordanCouplingPacket_carrier_source_obligation packet sourceLeftUnary
      sourceRightUnary decompositionUnary classifierUnary
  have ledgerSelf : hsame ledger ledger :=
    hsame_refl ledger
  have cert :
      SemanticNameCert (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger) (fun row : BHist => hsame row ledger)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger ledgerSelf
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows rowCarrier
        exact hsame_trans (hsame_symm sameRows) rowCarrier
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert rows

end BEDC.Derived.ClebschGordanUp
