import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {L U A W R E H C P N sealRead consumer : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg →
      Cont W R sealRead →
        Cont sealRead H consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory sealRead ∧
              UnaryHistory consumer ∧ Cont W R sealRead ∧ Cont sealRead H consumer ∧
                PkgSig bundle P pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory PkgSig
  intro carrier sealRoute consumerRoute consumerSig
  obtain ⟨unaryR, _unaryA, _handoffRoute, _sameLU, unaryW, routeWC, sameH,
    pkgSig, _sameN⟩ := carrier
  have unaryC : UnaryHistory C := unary_cont_closed unaryW unaryR routeWC
  have unaryH : UnaryHistory H :=
    unary_transport (unary_append_closed unaryC unaryW) (hsame_symm sameH)
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryW unaryR sealRoute
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unarySeal unaryH consumerRoute
  exact
    ⟨unaryW, unaryR, unaryH, unarySeal, unaryConsumer, sealRoute, consumerRoute, pkgSig,
      consumerSig⟩

end BEDC.Derived.LocatedSupremumUp
