import BEDC.Derived.CurryHowardUp

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

theorem CurryHowardCutBetaPacket_classifier_exhaustion [AskSetup] [PackageSetup]
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
                                hsame proofProgram (append conclusion appEndpoint) ∧
                                  hsame bridge (append provenance proofProgram) ∧
                                    PkgSig bundle conclusionProvenance pkg ∧
                                      PkgSig bundle bridge pkg := by
  intro firstOrderCarrier deductionStepUnary conclusionRow conclusionSig conclusionPkg funCarrier
    argCarrier appPayloadRow appTree appEndpointRow proofProgramRow provenanceRow bridgePkg
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
  have appPayloadUnary : UnaryHistory appPayload :=
    unary_cont_closed funCarrier.right.right.left argCarrier.right.right.left appPayloadRow
  have appEndpointUnary : UnaryHistory appEndpoint :=
    appTree.right.right.left.left
  have appCarrier :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic appTag appPayload appEndpoint :=
    And.intro appTree
      (And.intro appPayloadUnary
        (And.intro appEndpointUnary appEndpointRow))
  have proofSelf : hsame proofProgram proofProgram :=
    hsame_refl proofProgram
  have cert :
      SemanticNameCert (fun h : BHist => hsame h proofProgram)
        (fun h : BHist => hsame h proofProgram)
        (fun h : BHist => hsame h proofProgram) hsame := {
    core := {
      carrier_inhabited := Exists.intro proofProgram proofSelf
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
  have _appObject :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic appTag appPayload appEndpoint :=
    appCarrier
  exact And.intro cert
    (And.intro endpointRows.right.right.left
      (And.intro endpointRows.right.right.right.left
        (And.intro conclusionPkg endpointRows.right.right.right.right)))

end BEDC.Derived.CurryHowardUp
