import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessVisionConcretization [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont routes name publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory routes ->
            UnaryHistory name ->
              Cont basic eta analytic ∧ Cont analytic functional transports ∧
                Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                  UnaryHistory publicRead ∧ hsame publicRead (append routes name) ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesNamePublic publicPkg routesUnary nameUnary
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary routesNamePublic
  exact
    ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
      transportsRoutesProvenance, publicUnary, routesNamePublic, namePkg, provenancePkg,
      publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
