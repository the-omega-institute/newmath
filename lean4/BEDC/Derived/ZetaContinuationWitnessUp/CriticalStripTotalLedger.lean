import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessCriticalStripTotalLedger [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaRead
      gammaRead criticalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta etaRead ->
        Cont pole zeroLedger gammaRead ->
          Cont routes name criticalRead ->
            UnaryHistory basic ->
              UnaryHistory eta ->
                UnaryHistory pole ->
                  UnaryHistory zeroLedger ->
                    UnaryHistory routes ->
                      UnaryHistory name ->
                        PkgSig bundle criticalRead pkg ->
                          UnaryHistory etaRead ∧ UnaryHistory gammaRead ∧
                            UnaryHistory criticalRead ∧ Cont basic eta etaRead ∧
                              Cont pole zeroLedger gammaRead ∧ Cont routes name criticalRead ∧
                                hsame criticalRead (append routes name) ∧
                                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle criticalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet basicEtaRead poleZeroGammaRead routesNameCritical basicUnary etaUnary poleUnary
    zeroLedgerUnary routesUnary nameUnary criticalPkg
  obtain ⟨_basicAnalytic, _analyticTransports, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed basicUnary etaUnary basicEtaRead
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed poleUnary zeroLedgerUnary poleZeroGammaRead
  have criticalReadUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary routesNameCritical
  exact
    ⟨etaReadUnary, gammaReadUnary, criticalReadUnary, basicEtaRead, poleZeroGammaRead,
      routesNameCritical, routesNameCritical, namePkg, provenancePkg, criticalPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
