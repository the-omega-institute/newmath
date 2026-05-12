import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailSelectorPacket [AskSetup] [PackageSetup]
    (precision stream regularity dyadic «seal» witness transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory regularity ∧
    UnaryHistory dyadic ∧ UnaryHistory «seal» ∧ UnaryHistory witness ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont stream regularity witness ∧ Cont witness dyadic «seal» ∧
          Cont «seal» transport routes ∧ Cont routes provenance name ∧ PkgSig bundle name pkg

theorem RegularCauchyTailSelectorPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision stream regularity dyadic «seal» witness transport routes provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailSelectorPacket precision stream regularity dyadic «seal» witness transport
        routes provenance name bundle pkg ->
      Cont witness regularity consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory regularity ∧
            UnaryHistory dyadic ∧ UnaryHistory «seal» ∧ UnaryHistory witness ∧
              UnaryHistory consumer ∧ Cont stream regularity witness ∧
                Cont witness dyadic «seal» ∧ Cont witness regularity consumer ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet witnessRegularityConsumer consumerPkg
  obtain ⟨precisionUnary, streamUnary, regularityUnary, dyadicUnary, sealUnary, witnessUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameUnary, streamRegularityWitness,
    witnessDyadicSeal, _sealTransportRoutes, _routesProvenanceName, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed witnessUnary regularityUnary witnessRegularityConsumer
  exact
    ⟨precisionUnary, streamUnary, regularityUnary, dyadicUnary, sealUnary, witnessUnary,
      consumerUnary, streamRegularityWitness, witnessDyadicSeal, witnessRegularityConsumer,
      namePkg, consumerPkg⟩

theorem RegularCauchyTailSelectorPacket_precision_window_exactness [AskSetup] [PackageSetup]
    {precision stream regularity dyadic «seal» witness transport routes provenance name
      witnessPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailSelectorPacket precision stream regularity dyadic «seal» witness transport
        routes provenance name bundle pkg ->
      Cont stream regularity witnessPrime ->
        UnaryHistory witnessPrime ∧ hsame witness witnessPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet streamRegularityWitnessPrime
  obtain ⟨_precisionUnary, streamUnary, regularityUnary, _dyadicUnary, _sealUnary,
    _witnessUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    streamRegularityWitness, _witnessDyadicSeal, _sealTransportRoutes, _routesProvenanceName,
    _namePkg⟩ := packet
  have witnessPrimeUnary : UnaryHistory witnessPrime :=
    unary_cont_closed streamUnary regularityUnary streamRegularityWitnessPrime
  have sameWitness : hsame witness witnessPrime :=
    cont_respects_hsame (hsame_refl stream) (hsame_refl regularity) streamRegularityWitness
      streamRegularityWitnessPrime
  exact ⟨witnessPrimeUnary, sameWitness⟩

end BEDC.Derived.RegularCauchyTailSelectorUp
