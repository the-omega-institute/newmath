import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessLedgerScope [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont routes name publicRead ->
        PkgSig bundle publicRead pkg ->
          Cont basic eta analytic ∧ Cont analytic functional transports ∧
            Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
              Cont routes name publicRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro packet publicRoute publicPkg
  obtain ⟨basicRoute, analyticRoute, poleRoute, transportRoute, namePkg,
    provenancePkg⟩ := packet
  exact
    ⟨basicRoute, analyticRoute, poleRoute, transportRoute, publicRoute, namePkg,
      provenancePkg, publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
