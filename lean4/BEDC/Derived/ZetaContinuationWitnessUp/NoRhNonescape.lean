import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_no_rh_nonescape [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg ->
      UnaryHistory routes ->
      UnaryHistory name ->
      Cont routes name criticalRead ->
        UnaryHistory criticalRead ∧ hsame criticalRead (append routes name) ∧
          Cont basic eta analytic ∧ Cont analytic functional transports ∧
            Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
              PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameCritical
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary routesNameCritical
  exact
    ⟨criticalUnary, routesNameCritical, basicEtaAnalytic, analyticFunctionalTransports,
      poleZeroLedgerGamma, transportsRoutesProvenance, namePkg, provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
