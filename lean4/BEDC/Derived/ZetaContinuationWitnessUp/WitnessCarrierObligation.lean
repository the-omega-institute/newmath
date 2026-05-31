import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_carrier_obligation [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      exposed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name exposed ->
            PkgSig bundle exposed pkg ->
              UnaryHistory exposed ∧ Cont basic eta analytic ∧
                Cont analytic functional transports ∧ Cont pole zeroLedger gamma ∧
                  Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle exposed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet routesUnary nameUnary exposedRoute exposedPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have exposedUnary : UnaryHistory exposed :=
    unary_cont_closed routesUnary nameUnary exposedRoute
  exact
    ⟨exposedUnary, basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
      transportsRoutesProvenance, namePkg, provenancePkg, exposedPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
