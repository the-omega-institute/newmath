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

theorem CurryHowardCutBetaPacket_endpoint_exactness [AskSetup] [PackageSetup]
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
                                    hsame bridge (append provenance proofProgram) ∧
                                      PkgSig bundle bridge pkg := by
  intro firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg funCarrier
    argCarrier appPayloadRow appTree appEndpointRow proofProgramRow provenanceRow bridgePkg
  have bridgeRows :=
    CurryHowardCutBetaPacket_bridge_obligation
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (formulaProvenance := formulaProvenance)
      (deductionStep := deductionStep) (conclusion := conclusion)
      (conclusionProvenance := conclusionProvenance) (graph := graph) (edge := edge)
      (connected := connected) (acyclic := acyclic) (funTag := funTag)
      (funPayload := funPayload) (funEndpoint := funEndpoint) (argTag := argTag)
      (argPayload := argPayload) (argEndpoint := argEndpoint) (appPayload := appPayload)
      (appTag := appTag) (appEndpoint := appEndpoint) (proofProgram := proofProgram)
      (provenance := provenance) (bridge := bridge) (bundle := bundle) (pkg := pkg)
      firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg funCarrier
      argCarrier appPayloadRow appTree appEndpointRow proofProgramRow provenanceRow bridgePkg
  exact And.intro bridgeRows.left
    (And.intro bridgeRows.right.left
      (And.intro bridgeRows.right.right.left
        (And.intro provenanceRow bridgeRows.right.right.right)))

theorem CurryHowardCutBetaPacket_classifier_endpoint_transport [AskSetup] [PackageSetup]
    {conclusion conclusion' appEndpoint appEndpoint' proofProgram proofProgram' provenance bridge
      bridge' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont conclusion appEndpoint proofProgram ->
      hsame conclusion conclusion' ->
        hsame appEndpoint appEndpoint' ->
          Cont conclusion' appEndpoint' proofProgram' ->
            Cont provenance proofProgram bridge ->
              Cont provenance proofProgram' bridge' ->
                PkgSig bundle bridge pkg ->
                  PkgSig bundle bridge' pkg ->
                    hsame proofProgram proofProgram' ∧ hsame bridge bridge' ∧
                      PkgSig bundle bridge' pkg := by
  intro proofProgramRow sameConclusion sameEndpoint proofProgramRow' provenanceRow
    provenanceRow' _bridgePkg bridgePkg'
  have proofProgramSame : hsame proofProgram proofProgram' :=
    cont_respects_hsame sameConclusion sameEndpoint proofProgramRow proofProgramRow'
  have bridgeSame : hsame bridge bridge' :=
    cont_respects_hsame (hsame_refl provenance) proofProgramSame provenanceRow provenanceRow'
  exact And.intro proofProgramSame (And.intro bridgeSame bridgePkg')

theorem CurryHowardCutBetaPacket_source_obligation_surface [AskSetup] [PackageSetup]
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
                                    hsame bridge (append provenance proofProgram) ∧
                                      PkgSig bundle conclusionProvenance pkg ∧
                                        PkgSig bundle bridge pkg := by
  intro firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg funCarrier
    argCarrier appPayloadRow appTree appEndpointRow proofProgramRow provenanceRow bridgePkg
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
      (And.intro proofProgramRow
        (And.intro provenanceRow
          (And.intro conclusionPkg bridgePkg))))

end BEDC.Derived.CurryHowardUp
