import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessGammaLedgerExhaustion [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      gammaRead poleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      Cont pole zeroLedger gammaRead →
        Cont gamma transports poleRead →
          PkgSig bundle poleRead pkg →
            UnaryHistory pole →
              UnaryHistory zeroLedger →
                UnaryHistory transports →
                  UnaryHistory gammaRead ∧ UnaryHistory poleRead ∧
                    Cont pole zeroLedger gammaRead ∧ Cont gamma transports poleRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle poleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet gammaReadRoute poleReadRoute poleReadPkg poleUnary zeroLedgerUnary
    transportsUnary
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have gammaUnary : UnaryHistory gamma :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroLedgerGamma
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed poleUnary zeroLedgerUnary gammaReadRoute
  have poleReadUnary : UnaryHistory poleRead :=
    unary_cont_closed gammaUnary transportsUnary poleReadRoute
  exact
    ⟨gammaReadUnary, poleReadUnary, gammaReadRoute, poleReadRoute, namePkg, provenancePkg,
      poleReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
