import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_critical_strip_bridge_row [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont pole zeroLedger' gamma' →
            Cont transports' routes provenance' →
              PkgSig bundle name' pkg →
                PkgSig bundle provenance' pkg →
                  hsame eta eta' →
                    hsame zeroLedger zeroLedger' →
                      hsame name name' →
                        ZetaContinuationWitnessPacket basic eta' analytic' pole functional
                            zeroLedger' gamma' transports' routes provenance' name' bundle pkg ∧
                          hsame analytic analytic' ∧ hsame transports transports' ∧
                            hsame provenance provenance' ∧ hsame gamma gamma' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro packet basicRoute functionalRoute gammaRoute provenanceRoute namePkg provenancePkg
    etaSame zeroLedgerSame nameSame
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, _oldNamePkg, provenancePkg'⟩ :=
    ledger
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, _oldNamePkg', _oldProvenancePkg⟩ := gammaBoundary
  cases nameSame
  exact
    ⟨⟨basicRoute, functionalRoute, gammaRoute, provenanceRoute, namePkg, provenancePkg'⟩,
      analyticSame, transportsSame, provenanceSame, gammaSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
