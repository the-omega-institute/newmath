import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.WindowRoute

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp.RegSeqRatSealFactorization

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorCarrier_regseqrat_seal_factorization [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName route sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont stream readback route →
        Cont route realSeal sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
              UnaryHistory route ∧ UnaryHistory sealRead ∧ Cont stream readback route ∧
                Cont route realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont PkgSig UnaryHistory
  intro carrier streamReadback routeSeal sealPkg
  obtain ⟨_epsilonUnary, _windowUnary, streamUnary, readbackUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed streamUnary readbackUnary streamReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed routeUnary realSealUnary routeSeal
  exact
    ⟨streamUnary, readbackUnary, realSealUnary, routeUnary, sealUnary, streamReadback,
      routeSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp.RegSeqRatSealFactorization
