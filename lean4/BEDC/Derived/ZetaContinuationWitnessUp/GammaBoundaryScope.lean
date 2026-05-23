import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_gamma_boundary_scope [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name gammaRead ->
            PkgSig bundle gammaRead pkg ->
              Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                UnaryHistory gammaRead ∧ hsame gammaRead (append routes name) ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle gammaRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary gammaRoute gammaPkg
  obtain ⟨_basicEtaAnalytic, _analyticTransport, poleGamma, transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary gammaRoute
  exact
    ⟨poleGamma, transportProvenance, gammaReadUnary, gammaRoute, namePkg, provenancePkg,
      gammaPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
