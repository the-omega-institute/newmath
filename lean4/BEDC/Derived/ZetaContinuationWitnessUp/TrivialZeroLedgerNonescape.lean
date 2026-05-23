import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_trivial_zero_ledger_nonescape [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name zeroRead
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory zeroLedger ->
        UnaryHistory gamma ->
          Cont zeroLedger gamma zeroRead ->
            PkgSig bundle zeroRead pkg ->
              UnaryHistory zeroRead ∧ hsame zeroRead (append zeroLedger gamma) ∧
                Cont pole zeroLedger gamma ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle zeroRead pkg ∧
                    (Cont zeroRead (BHist.e0 hostTail) zeroLedger -> False) ∧
                      (Cont zeroRead (BHist.e1 hostTail) zeroLedger -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet zeroLedgerUnary gammaUnary zeroGammaRead zeroReadPkg
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroLedgerUnary gammaUnary zeroGammaRead
  have e0Refusal : Cont zeroRead (BHist.e0 hostTail) zeroLedger -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.left zeroGammaRead back
  have e1Refusal : Cont zeroRead (BHist.e1 hostTail) zeroLedger -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.right zeroGammaRead back
  exact
    ⟨zeroReadUnary, zeroGammaRead, poleZeroLedgerGamma, namePkg, provenancePkg, zeroReadPkg,
      e0Refusal, e1Refusal⟩

end BEDC.Derived.ZetaContinuationWitnessUp
