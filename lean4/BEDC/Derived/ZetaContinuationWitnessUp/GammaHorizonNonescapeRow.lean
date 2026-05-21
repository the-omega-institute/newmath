import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_gamma_horizon_nonescape_row [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      gammaRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont functional gamma gammaRead →
        Cont gammaRead name publicRead →
          PkgSig bundle publicRead pkg →
            Cont pole zeroLedger gamma ∧ Cont functional gamma gammaRead ∧
              Cont gammaRead name publicRead ∧ Cont transports routes provenance ∧
                PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro packet gammaRoute publicRoute publicPkg
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, poleGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  exact
    ⟨poleGamma, gammaRoute, publicRoute, transportsRoutesProvenance, namePkg,
      provenancePkg, publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
