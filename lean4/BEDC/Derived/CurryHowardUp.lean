import BEDC.Derived.FirstOrderUp
import BEDC.Derived.LambdaCalcUp
import BEDC.Derived.TreeUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CurryHowardUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CurryHowardCutBetaPacket_public_namecert_boundary [AskSetup] [PackageSetup]
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
                              SemanticNameCert (fun h : BHist => hsame h proofProgram)
                                  (fun h : BHist => hsame h proofProgram)
                                  (fun h : BHist => hsame h proofProgram) hsame ∧
                                UnaryHistory conclusion ∧
                                  LambdaCalcBHistTermPacketCarrier graph edge connected acyclic
                                    appTag appPayload appEndpoint ∧
                                    hsame proofProgram (append conclusion appEndpoint) ∧
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
  have cert :
      SemanticNameCert (fun h : BHist => hsame h proofProgram)
        (fun h : BHist => hsame h proofProgram)
        (fun h : BHist => hsame h proofProgram) hsame := {
    core := {
      carrier_inhabited := Exists.intro proofProgram (hsame_refl proofProgram)
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro bridgeRows.left
      (And.intro bridgeRows.right.left
        (And.intro bridgeRows.right.right.left bridgeRows.right.right.right)))

theorem CurryHowardCutBetaPacket_endpoint_classifier_obligation_surface [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint formulaProvenance deductionStep conclusion conclusion' conclusionProvenance
      graph edge connected acyclic funTag funPayload funEndpoint argTag argPayload argEndpoint
      appPayload appTag appEndpoint appEndpoint' proofProgram proofProgram' provenance bridge
      bridge' : BHist}
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
                          hsame conclusion conclusion' ->
                            hsame appEndpoint appEndpoint' ->
                              Cont conclusion' appEndpoint' proofProgram' ->
                                Cont provenance proofProgram bridge ->
                                  Cont provenance proofProgram' bridge' ->
                                    PkgSig bundle bridge pkg ->
                                      PkgSig bundle bridge' pkg ->
                                        hsame proofProgram proofProgram' ∧
                                          hsame bridge bridge' ∧ UnaryHistory conclusion ∧
                                            LambdaCalcBHistTermPacketCarrier graph edge connected
                                              acyclic appTag appPayload appEndpoint ∧
                                              PkgSig bundle bridge' pkg := by
  intro firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg funCarrier
    argCarrier appPayloadRow appTree appEndpointRow proofProgramRow sameConclusion sameEndpoint
    proofProgramRow' provenanceRow provenanceRow' bridgePkg bridgePkg'
  have endpointRows :=
    CurryHowardCutBetaPacket_endpoint_exactness
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
  have transportedRows :=
    CurryHowardCutBetaPacket_classifier_endpoint_transport
      (conclusion := conclusion) (conclusion' := conclusion')
      (appEndpoint := appEndpoint) (appEndpoint' := appEndpoint')
      (proofProgram := proofProgram) (proofProgram' := proofProgram')
      (provenance := provenance) (bridge := bridge) (bridge' := bridge')
      (bundle := bundle) (pkg := pkg) proofProgramRow sameConclusion sameEndpoint
      proofProgramRow' provenanceRow provenanceRow' bridgePkg bridgePkg'
  exact And.intro transportedRows.left
    (And.intro transportedRows.right.left
      (And.intro endpointRows.left
        (And.intro endpointRows.right.left transportedRows.right.right)))

end BEDC.Derived.CurryHowardUp
