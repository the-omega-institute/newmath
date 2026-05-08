import BEDC.Derived.SeparableExtUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.SeparableExtUp

def GaloisExtSourcePacket [AskSetup] [PackageSetup]
    (fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
      separable bundle pkg ∧
    UnaryHistory normality ∧ UnaryHistory separability ∧
      Cont fieldExt separable provenance ∧ Cont normality separability classifier ∧
        Cont provenance classifier endpoint ∧ PkgSig bundle endpoint pkg

theorem GaloisExtSourcePacket_normality_obligation_row [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
          separable bundle pkg ∧
        UnaryHistory normality ∧ hsame provenance (append fieldExt separable) ∧
          hsame classifier (append normality separability) ∧
            hsame endpoint (append provenance classifier) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.right.left
        (And.intro packet.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.left
            packet.right.right.right.right.right.right))))

theorem GaloisExtSourcePacket_classifier_transport
    {field field' separable separable' normal normal' simple simple' classifier classifier'
      provenance provenance' ledger ledger' : BHist} :
    UnaryHistory field ->
      UnaryHistory separable ->
        UnaryHistory normal ->
          UnaryHistory simple ->
            hsame field field' ->
              hsame separable separable' ->
                hsame normal normal' ->
                  hsame simple simple' ->
                    Cont field separable classifier ->
                      Cont normal simple provenance ->
                        Cont classifier provenance ledger ->
                          Cont field' separable' classifier' ->
                            Cont normal' simple' provenance' ->
                              Cont classifier' provenance' ledger' ->
                                UnaryHistory classifier' ∧ UnaryHistory provenance' ∧
                                  UnaryHistory ledger' ∧ hsame classifier classifier' ∧
                                    hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro fieldUnary separableUnary normalUnary simpleUnary sameField sameSeparable sameNormal
    sameSimple classifierCont provenanceCont ledgerCont classifierCont' provenanceCont'
    ledgerCont'
  have fieldUnary' : UnaryHistory field' :=
    unary_transport fieldUnary sameField
  have separableUnary' : UnaryHistory separable' :=
    unary_transport separableUnary sameSeparable
  have normalUnary' : UnaryHistory normal' :=
    unary_transport normalUnary sameNormal
  have simpleUnary' : UnaryHistory simple' :=
    unary_transport simpleUnary sameSimple
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed fieldUnary' separableUnary' classifierCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed normalUnary' simpleUnary' provenanceCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed classifierUnary' provenanceUnary' ledgerCont'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameField sameSeparable classifierCont classifierCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameNormal sameSimple provenanceCont provenanceCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameClassifier sameProvenance ledgerCont ledgerCont'
  exact And.intro classifierUnary'
    (And.intro provenanceUnary'
      (And.intro ledgerUnary'
        (And.intro sameClassifier
          (And.intro sameProvenance sameLedger))))

theorem GaloisExtSourcePacket_endpoint_empty_inversion [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      hsame endpoint BHist.Empty ->
        hsame fieldExt BHist.Empty /\ hsame separable BHist.Empty /\
          hsame normality BHist.Empty /\ hsame separability BHist.Empty := by
  intro packet endpointEmpty
  have endpointCont : Cont provenance classifier endpoint :=
    packet.right.right.right.right.right.left
  have provenanceClassifierEmpty :
      Cont provenance classifier BHist.Empty :=
    cont_result_hsame_transport endpointCont endpointEmpty
  have provenanceClassifierParts := cont_empty_result_inversion provenanceClassifierEmpty
  have provenanceEmpty : hsame provenance BHist.Empty :=
    provenanceClassifierParts.left
  have classifierEmpty : hsame classifier BHist.Empty :=
    provenanceClassifierParts.right
  have fieldSeparableCont : Cont fieldExt separable provenance :=
    packet.right.right.right.left
  have fieldSeparableEmpty :
      Cont fieldExt separable BHist.Empty :=
    cont_result_hsame_transport fieldSeparableCont provenanceEmpty
  have fieldSeparableParts := cont_empty_result_inversion fieldSeparableEmpty
  have normalitySeparabilityCont : Cont normality separability classifier :=
    packet.right.right.right.right.left
  have normalitySeparabilityEmpty :
      Cont normality separability BHist.Empty :=
    cont_result_hsame_transport normalitySeparabilityCont classifierEmpty
  have normalitySeparabilityParts := cont_empty_result_inversion normalitySeparabilityEmpty
  exact And.intro fieldSeparableParts.left
    (And.intro fieldSeparableParts.right
      (And.intro normalitySeparabilityParts.left normalitySeparabilityParts.right))

end BEDC.Derived.GaloisExtUp
