import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FirstOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def FirstOrderBHistSyntaxCarrier [AskSetup] [PackageSetup]
    (symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symbolSource ∧
    UnaryHistory treeSource ∧
      UnaryHistory variableLedger ∧
        UnaryHistory relationSymbol ∧
          UnaryHistory functionSymbol ∧
            Cont treeSource variableLedger treeEndpoint ∧
              Cont treeEndpoint relationSymbol formulaEndpoint ∧
                SigRel bundle formulaEndpoint provenance ∧
                  PkgSig bundle provenance pkg

theorem FirstOrderBHistSyntaxCarrier_endpoint_unary [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
      treeEndpoint formulaEndpoint provenance bundle pkg ->
        UnaryHistory treeEndpoint ∧ UnaryHistory formulaEndpoint := by
  intro carrier
  have treeEndpointUnary : UnaryHistory treeEndpoint :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have formulaEndpointUnary : UnaryHistory formulaEndpoint :=
    unary_cont_closed treeEndpointUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  exact And.intro treeEndpointUnary formulaEndpointUnary

theorem FirstOrderBHistSyntaxCarrier_formula_carrier_obligation [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol
      functionSymbol treeEndpoint formulaEndpoint provenance bundle pkg ->
        UnaryHistory symbolSource ∧
          UnaryHistory treeSource ∧
            UnaryHistory relationSymbol ∧
              UnaryHistory functionSymbol ∧
                UnaryHistory formulaEndpoint ∧
                  SigRel bundle formulaEndpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have endpointUnary :=
    FirstOrderBHistSyntaxCarrier_endpoint_unary
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := provenance)
      (bundle := bundle) (pkg := pkg) carrier
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro endpointUnary.right
              (And.intro carrier.right.right.right.right.right.right.right.left
                carrier.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.FirstOrderUp
