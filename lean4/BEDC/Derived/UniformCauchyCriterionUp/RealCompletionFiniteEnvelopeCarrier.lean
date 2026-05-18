import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCauchyCriterionRealCompletionFiniteEnvelopeCarrier [AskSetup] [PackageSetup]
    (stream readback dyadic sealRow completion transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory sealRow ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ Cont stream readback dyadic ∧ Cont dyadic sealRow completion ∧
        PkgSig bundle name pkg

theorem UniformCauchyCriterionRealCompletionFiniteEnvelopeCarrier_rows
    [AskSetup] [PackageSetup]
    {stream readback dyadic sealRow completion transport replay provenance name envelope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionRealCompletionFiniteEnvelopeCarrier stream readback dyadic sealRow
        completion transport replay provenance name bundle pkg →
      PkgSig bundle envelope pkg →
        UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
          UnaryHistory sealRow ∧ UnaryHistory completion ∧ Cont stream readback dyadic ∧
            Cont dyadic sealRow completion ∧ PkgSig bundle envelope pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopePkg
  obtain ⟨streamUnary, readbackUnary, dyadicUnary, sealRowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, streamReadbackDyadic,
    dyadicSealCompletion, _namePkg⟩ := carrier
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed dyadicUnary sealRowUnary dyadicSealCompletion
  exact
    ⟨streamUnary, readbackUnary, dyadicUnary, sealRowUnary, completionUnary,
      streamReadbackDyadic, dyadicSealCompletion, envelopePkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
