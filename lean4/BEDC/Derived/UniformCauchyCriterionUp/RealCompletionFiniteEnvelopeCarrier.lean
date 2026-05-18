import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCauchyCriterionRealCompletionFiniteEnvelopeCarrier [AskSetup] [PackageSetup]
    (index windows modulus tolerance tail sealRow transports routes provenance name regseq dyadic
      cauchySeal realExport envelopeRoute : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
      provenance name bundle pkg ∧
    UnaryHistory regseq ∧ UnaryHistory dyadic ∧ UnaryHistory cauchySeal ∧
      UnaryHistory realExport ∧ Cont windows regseq dyadic ∧
        Cont dyadic cauchySeal realExport ∧ Cont realExport name envelopeRoute ∧
          PkgSig bundle envelopeRoute pkg

theorem UniformCauchyCriterionRealCompletionFiniteEnvelopeCarrier_consumer_row
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseq dyadic
      cauchySeal realExport envelopeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionRealCompletionFiniteEnvelopeCarrier index windows modulus tolerance tail
        sealRow transports routes provenance name regseq dyadic cauchySeal realExport
        envelopeRoute bundle pkg →
      UnaryHistory windows ∧ UnaryHistory regseq ∧ UnaryHistory dyadic ∧
        UnaryHistory cauchySeal ∧ UnaryHistory realExport ∧ UnaryHistory envelopeRoute ∧
          Cont windows regseq dyadic ∧ Cont dyadic cauchySeal realExport ∧
            Cont realExport name envelopeRoute ∧ PkgSig bundle name pkg ∧
              PkgSig bundle envelopeRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  rcases carrier with
    ⟨packet, regseqUnary, dyadicUnary, cauchySealUnary, realExportUnary,
      windowsRegseqDyadic, dyadicSealReal, realNameEnvelope, envelopePkg⟩
  rcases packet with
    ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
      _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, nameUnary,
      _indexWindowsModulus, _modulusToleranceTail, _tailSealTransports,
      _transportsRoutesProvenance, namePkg⟩
  have envelopeUnary : UnaryHistory envelopeRoute :=
    unary_cont_closed realExportUnary nameUnary realNameEnvelope
  exact
    ⟨windowsUnary, regseqUnary, dyadicUnary, cauchySealUnary, realExportUnary,
      envelopeUnary, windowsRegseqDyadic, dyadicSealReal, realNameEnvelope, namePkg,
      envelopePkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
