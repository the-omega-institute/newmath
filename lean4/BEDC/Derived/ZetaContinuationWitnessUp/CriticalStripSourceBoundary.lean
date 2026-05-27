import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_critical_strip_source_boundary
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory provenance ->
        UnaryHistory name ->
          Cont provenance name criticalRead ->
            Cont basic eta analytic ∧ Cont analytic functional transports ∧
              Cont pole zeroLedger gamma ∧ UnaryHistory criticalRead ∧
                Cont provenance name criticalRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet provenanceUnary nameUnary criticalRoute
  obtain ⟨basicAnalytic, analyticTransports, poleGamma, _transportsProvenance,
    namePkg, provenancePkg⟩ := packet
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed provenanceUnary nameUnary criticalRoute
  exact
    ⟨basicAnalytic, analyticTransports, poleGamma, criticalUnary, criticalRoute,
      namePkg, provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
