import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_classifier_stability [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' zeroLedger' gamma' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont pole zeroLedger' gamma' ->
            Cont transports' routes provenance' ->
              PkgSig bundle provenance' pkg ->
                hsame eta eta' ->
                  hsame zeroLedger zeroLedger' ->
                    hsame analytic analytic' ∧ hsame transports transports' ∧
                      hsame gamma gamma' ∧ hsame provenance provenance' ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig
  intro packet basicRoute functionalRoute gammaRoute provenanceRoute provenancePkg etaSame
    zeroLedgerSame
  obtain ⟨basicAnalytic, analyticTransport, poleGamma, transportProvenance, namePkg,
    _provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport functionalRoute
  have gammaSame : hsame gamma gamma' :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleGamma gammaRoute
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame transportsSame (hsame_refl routes) transportProvenance provenanceRoute
  exact
    ⟨analyticSame, transportsSame, gammaSame, provenanceSame, namePkg, provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
