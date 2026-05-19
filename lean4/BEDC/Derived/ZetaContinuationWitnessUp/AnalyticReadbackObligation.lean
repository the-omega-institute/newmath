import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_analytic_readback_obligation
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' gammaRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont pole zeroLedger gammaRead →
            Cont transports' routes readback →
              PkgSig bundle readback pkg →
                hsame eta eta' →
                  hsame zeroLedger zeroLedger →
                    hsame analytic analytic' ∧ hsame transports transports' ∧
                      hsame gamma gammaRead ∧ Cont pole zeroLedger gammaRead ∧
                        Cont transports' routes readback ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro packet basicRoute functionalRoute gammaRoute readbackRoute readbackPkg etaSame
    zeroLedgerSame
  obtain ⟨basicAnalytic, analyticTransport, poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport
      functionalRoute
  have gammaSame : hsame gamma gammaRead :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleGamma gammaRoute
  exact
    ⟨analyticSame, transportsSame, gammaSame, gammaRoute, readbackRoute, namePkg,
      provenancePkg, readbackPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
