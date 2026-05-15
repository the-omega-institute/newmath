import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CrossHistCausalRateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CrossHistCausalRateCarrier [AskSetup] [PackageSetup]
    (observerA observerB causalRoutes maximumRate observerSymmetry noGlobalFrame transports
      continuation provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory observerA ∧ UnaryHistory observerB ∧ UnaryHistory causalRoutes ∧
    UnaryHistory maximumRate ∧ UnaryHistory observerSymmetry ∧ UnaryHistory noGlobalFrame ∧
      UnaryHistory transports ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont observerA observerB causalRoutes ∧
          Cont causalRoutes continuation maximumRate ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem CrossHistCausalRateCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {observerA observerB causalRoutes maximumRate observerSymmetry noGlobalFrame transports
      continuation provenance localName replay rateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CrossHistCausalRateCarrier observerA observerB causalRoutes maximumRate observerSymmetry
        noGlobalFrame transports continuation provenance localName bundle pkg →
      Cont causalRoutes continuation replay →
        Cont replay maximumRate rateRead →
          PkgSig bundle rateRead pkg →
            UnaryHistory observerA ∧ UnaryHistory observerB ∧ UnaryHistory causalRoutes ∧
              UnaryHistory maximumRate ∧ UnaryHistory replay ∧ UnaryHistory rateRead ∧
                Cont causalRoutes continuation replay ∧ Cont replay maximumRate rateRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle rateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier replayRoute rateReadRoute rateReadPkg
  obtain ⟨observerAUnary, observerBUnary, causalRoutesUnary, maximumRateUnary,
    _observerSymmetryUnary, _noGlobalFrameUnary, _transportsUnary, continuationUnary,
    _provenanceUnary, _localNameUnary, _observerRoute, _maximumRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed causalRoutesUnary continuationUnary replayRoute
  have rateReadUnary : UnaryHistory rateRead :=
    unary_cont_closed replayUnary maximumRateUnary rateReadRoute
  exact
    ⟨observerAUnary, observerBUnary, causalRoutesUnary, maximumRateUnary, replayUnary,
      rateReadUnary, replayRoute, rateReadRoute, provenancePkg, localNamePkg, rateReadPkg⟩

end BEDC.Derived.CrossHistCausalRateUp
