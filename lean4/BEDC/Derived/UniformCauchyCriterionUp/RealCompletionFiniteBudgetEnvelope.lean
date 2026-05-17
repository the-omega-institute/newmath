import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_finite_budget_envelope
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name real
      completion envelope hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont sealRow provenance real →
        Cont real name completion →
          Cont completion routes envelope →
            PkgSig bundle envelope pkg →
              UnaryHistory envelope ∧ Cont sealRow provenance real ∧
                Cont real name completion ∧ Cont completion routes envelope ∧
                  PkgSig bundle envelope pkg ∧
                    (Cont envelope (BHist.e0 hostTail) real → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sealProvenanceReal realNameCompletion completionRoutesEnvelope envelopePkg
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
    sealRowUnary, _transportsUnary, routesUnary, provenanceUnary, nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have realUnary : UnaryHistory real :=
    unary_cont_closed sealRowUnary provenanceUnary sealProvenanceReal
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed realUnary nameUnary realNameCompletion
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed completionUnary routesUnary completionRoutesEnvelope
  exact
    ⟨envelopeUnary, sealProvenanceReal, realNameCompletion, completionRoutesEnvelope,
      envelopePkg,
      (fun back =>
        cont_triangle_cycle_right_zero_tail_absurd realNameCompletion
          completionRoutesEnvelope back)⟩

theorem UniformCauchyCriterionPacket_real_completion_finite_envelope
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name realRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow realRead ->
        Cont realRead transports completionRead ->
          PkgSig bundle realRead pkg ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tail ∧
                UnaryHistory realRead ∧ UnaryHistory completionRead ∧
                  Cont modulus tolerance tail ∧ Cont tail sealRow realRead ∧
                    Cont realRead transports completionRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle realRead pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealRealRead realTransportCompletion realReadPkg completionReadPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realReadUnary transportsUnary realTransportCompletion
  exact
    ⟨windowsUnary, toleranceUnary, tailUnary, realReadUnary, completionReadUnary,
      modulusToleranceTail, tailSealRealRead, realTransportCompletion, namePkg, realReadPkg,
      completionReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
