import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_gamma_horizon_consumer_boundary
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont gamma routes gammaRead →
        PkgSig bundle gammaRead pkg →
          UnaryHistory routes →
            UnaryHistory gamma →
              UnaryHistory gammaRead ∧ Cont gamma routes gammaRead ∧
                Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle gammaRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet gammaRoutesRead gammaReadPkg routesUnary gammaUnary
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, _provenancePkg⟩ := packet
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary routesUnary gammaRoutesRead
  exact
    ⟨gammaReadUnary, gammaRoutesRead, transportsRoutesProvenance, namePkg, gammaReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
