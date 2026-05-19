import BEDC.Derived.RealityConstrainedMethodologyLedgerUp.KernelCarrier

namespace BEDC.Derived.RealityConstrainedMethodologyLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedMethodologyLedgerUpgradeRouteDeterminacy [AskSetup] [PackageSetup]
    {X A O T I S D U F H C Q N exportRead upgradeRead upgradeRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedMethodologyLedgerCarrier X A O T I S D U F H C Q N bundle pkg ->
      Cont D U exportRead ->
        Cont exportRead S upgradeRead ->
          Cont exportRead S upgradeRead' ->
            PkgSig bundle upgradeRead pkg ->
              PkgSig bundle upgradeRead' pkg ->
                hsame upgradeRead upgradeRead' ∧ UnaryHistory exportRead ∧
                  UnaryHistory upgradeRead ∧ UnaryHistory upgradeRead' ∧
                    PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier exportRoute upgradeRoute upgradeRoute' _upgradePkg _upgradePkg'
  rcases carrier with
    ⟨_xUnary, _aUnary, _oUnary, _tUnary, _iUnary, scopeUnary, refusalUnary,
      upgradeUnary, _failureUnary, _sameH, _scopeRefusalUpgrade, _upgradeFailureConsumer,
      _consumerProvenanceName, qPkg⟩
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed refusalUnary upgradeUnary exportRoute
  have upgradeReadUnary : UnaryHistory upgradeRead :=
    unary_cont_closed exportUnary scopeUnary upgradeRoute
  have upgradeReadUnary' : UnaryHistory upgradeRead' :=
    unary_cont_closed exportUnary scopeUnary upgradeRoute'
  have sameUpgrade : hsame upgradeRead upgradeRead' :=
    cont_deterministic upgradeRoute upgradeRoute'
  exact ⟨sameUpgrade, exportUnary, upgradeReadUnary, upgradeReadUnary', qPkg⟩

end BEDC.Derived.RealityConstrainedMethodologyLedgerUp
