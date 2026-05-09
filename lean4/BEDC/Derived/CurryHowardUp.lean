import BEDC.Derived.FirstOrderUp
import BEDC.Derived.LambdaCalcUp
import BEDC.Derived.TreeUp

namespace BEDC.Derived.CurryHowardUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.FirstOrderUp
open BEDC.Derived.LambdaCalcUp
open BEDC.Derived.TreeUp

theorem CurryHowardCutBetaPacket_bridge_obligation [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint formulaProvenance deductionStep conclusion conclusionProvenance graph edge
      connected acyclic funTag funPayload funEndpoint argTag argPayload argEndpoint appPayload appTag
      appEndpoint proofProgram provenance bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
        treeEndpoint formulaEndpoint formulaProvenance bundle pkg ->
      UnaryHistory deductionStep ->
        Cont formulaEndpoint deductionStep conclusion ->
          SigRel bundle conclusion conclusionProvenance ->
            PkgSig bundle conclusionProvenance pkg ->
              LambdaCalcBHistTermPacketCarrier graph edge connected acyclic funTag funPayload
                  funEndpoint ->
                LambdaCalcBHistTermPacketCarrier graph edge connected acyclic argTag argPayload
                    argEndpoint ->
                  Cont funEndpoint argEndpoint appPayload ->
                    TreeBHistCarrier graph edge connected acyclic appTag appEndpoint ->
                      Cont appTag appPayload appEndpoint ->
                        Cont conclusion appEndpoint proofProgram ->
                          Cont provenance proofProgram bridge ->
                            PkgSig bundle bridge pkg ->
                              UnaryHistory conclusion ∧
                                LambdaCalcBHistTermPacketCarrier graph edge connected acyclic appTag
                                  appPayload appEndpoint ∧
                                  hsame proofProgram (append conclusion appEndpoint) ∧
                                    PkgSig bundle bridge pkg := by
  intro firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg funCarrier
    argCarrier appPayloadRow appTree appEndpointRow proofProgramRow _provenanceRow bridgePkg
  have cutRows :=
    FirstOrderBHistSyntaxCarrier_deduction_endpoint_exactness
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := formulaProvenance)
      (deductionStep := deductionStep) (conclusion := conclusion)
      (conclusionProvenance := conclusionProvenance) (bundle := bundle) (pkg := pkg)
      firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg
  have appPayloadUnary : UnaryHistory appPayload :=
    unary_cont_closed funCarrier.right.right.left argCarrier.right.right.left appPayloadRow
  have appEndpointUnary : UnaryHistory appEndpoint :=
    appTree.right.right.left.left
  have appCarrier :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic appTag appPayload appEndpoint :=
    And.intro appTree
      (And.intro appPayloadUnary
        (And.intro appEndpointUnary appEndpointRow))
  exact And.intro cutRows.right.left
    (And.intro appCarrier
      (And.intro proofProgramRow bridgePkg))

end BEDC.Derived.CurryHowardUp
