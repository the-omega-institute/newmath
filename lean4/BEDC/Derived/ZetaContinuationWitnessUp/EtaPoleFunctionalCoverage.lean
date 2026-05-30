import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_eta_pole_functional_coverage [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaRead
      functionalRead gammaRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory eta →
        UnaryHistory functional →
          UnaryHistory gamma →
            UnaryHistory pole →
              UnaryHistory zeroLedger →
                Cont eta functional etaRead →
                  Cont functional gamma functionalRead →
                    Cont pole zeroLedger gammaRead →
                      Cont etaRead gammaRead exportRead →
                        PkgSig bundle exportRead pkg →
                          UnaryHistory etaRead ∧ UnaryHistory functionalRead ∧
                            UnaryHistory gammaRead ∧ UnaryHistory exportRead ∧
                              Cont eta functional etaRead ∧
                                Cont functional gamma functionalRead ∧
                                  Cont pole zeroLedger gammaRead ∧
                                    Cont etaRead gammaRead exportRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet etaUnary functionalUnary gammaUnary poleUnary zeroLedgerUnary etaFunctionalRead
    functionalGammaRead poleZeroLedgerRead etaGammaExportRead exportPkg
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary functionalUnary etaFunctionalRead
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalGammaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroLedgerRead
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed etaReadUnary gammaReadUnary etaGammaExportRead
  exact
    ⟨etaReadUnary, functionalReadUnary, gammaReadUnary, exportReadUnary, etaFunctionalRead,
      functionalGammaRead, poleZeroLedgerRead, etaGammaExportRead, namePkg, provenancePkg,
      exportPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
