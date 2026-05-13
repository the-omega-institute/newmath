import BEDC.Derived.RealCauchyCompletionUp
import BEDC.Derived.RegularCauchyDiagonalUp
import BEDC.Derived.RegularCauchyNameUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_name_normalization_handoff [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead sealRead : BHist}
    {schedule observation radius ledger nameSeal nameProvenance namecert nameEndpoint nameWindow
      nameReadback : BHist}
    {family modulus diagonalPacket compWindow compReadback dyadic compSeal compProvenance
      compLocalCert family' modulus' diagonal' compWindow' compReadback' dyadic' compSeal'
      compProvenance' compLocalCert' compConsumer compDownstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont regseqRead realSeal sealRead ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle sealRead pkg ->
                BEDC.Derived.RegularCauchyNameUp.RegularCauchyNameCarrier schedule
                    observation radius ledger nameSeal nameProvenance namecert nameEndpoint
                    bundle pkg ->
                  Cont schedule observation nameWindow ->
                    Cont nameWindow radius nameReadback ->
                      PkgSig bundle nameReadback pkg ->
                        BEDC.Derived.RealCauchyCompletionUp.RealCauchyCompletionCarrier family
                            modulus diagonalPacket compWindow compReadback dyadic compSeal
                            compProvenance compLocalCert bundle pkg ->
                          hsame family family' ->
                            hsame modulus modulus' ->
                              hsame compWindow compWindow' ->
                                hsame dyadic dyadic' ->
                                  hsame compLocalCert compLocalCert' ->
                                    Cont family' modulus' diagonal' ->
                                      Cont diagonal' compWindow' compReadback' ->
                                        Cont compReadback' dyadic' compSeal' ->
                                          Cont compSeal' compLocalCert' compProvenance' ->
                                            Cont compSeal' compLocalCert' compConsumer ->
                                              Cont compConsumer compProvenance' compDownstream ->
                                                PkgSig bundle compProvenance' pkg ->
                                                  PkgSig bundle compDownstream pkg ->
                                                    UnaryHistory completionRead ∧
                                                      UnaryHistory nameReadback ∧
                                                        UnaryHistory compConsumer ∧
                                                          UnaryHistory compDownstream ∧
                                                            hsame windowLedger sealRead ∧
                                                              hsame radius nameWindow ∧
                                                                hsame compProvenance
                                                                    compProvenance' ∧
                                                                  PkgSig bundle provenance pkg ∧
                                                                    PkgSig bundle nameEndpoint
                                                                        pkg ∧
                                                                      PkgSig bundle
                                                                        compDownstream pkg := by
  intro diagonalCarrier windowSelection completionRow sealReadRow completionPkg sealReadPkg
  intro nameCarrier scheduleObservationWindow windowRadiusReadback nameReadbackPkg
  intro completionCarrier sameFamily sameModulus sameWindow sameDyadic sameLocalCert
  intro familyModulusRow diagonalWindowRow readbackDyadicRow sealLocalProvenance
  intro sealLocalConsumer consumerDownstream compProvenancePkg compDownstreamPkg
  have diagonalHandoff :=
    RegularCauchyDiagonalCarrier_real_completion_handoff diagonalCarrier windowSelection
      completionRow sealReadRow completionPkg sealReadPkg
  obtain ⟨_selectedWindowUnary, completionUnary, _sealReadUnary, _completionRoute, _sealRoute,
    ledgerSameSealRead, provenancePkg, _completionPkgOut, _sealReadPkgOut⟩ := diagonalHandoff
  have nameLock :=
    BEDC.Derived.RegularCauchyNameUp.RegularCauchyNameCarrier_schedule_radius_lock nameCarrier
      scheduleObservationWindow windowRadiusReadback nameReadbackPkg
  obtain ⟨radiusSameWindow, _nameWindowUnary, nameReadbackUnary, _scheduleWindow,
    _windowReadback, nameEndpointPkg, _nameReadbackPkgOut⟩ := nameLock
  have completionHandoff :=
    BEDC.Derived.RealCauchyCompletionUp.RealCauchyCompletionCarrier_downstream_consumer_handoff
      completionCarrier sameFamily sameModulus sameWindow sameDyadic sameLocalCert
      familyModulusRow diagonalWindowRow readbackDyadicRow sealLocalProvenance
      sealLocalConsumer consumerDownstream compProvenancePkg compDownstreamPkg
  obtain ⟨_transportedCarrier, compConsumerUnary, compDownstreamUnary,
    sameCompletionProvenance⟩ := completionHandoff
  exact
    ⟨completionUnary, nameReadbackUnary, compConsumerUnary, compDownstreamUnary,
      ledgerSameSealRead, radiusSameWindow, sameCompletionProvenance, provenancePkg,
      nameEndpointPkg, compDownstreamPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
