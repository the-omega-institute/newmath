import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCauchyCriterionPublicExportSurface [AskSetup] [PackageSetup]
    (index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead publicRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
      provenance name bundle pkg ∧
    Cont index tail regseqRead ∧ Cont tail sealRow realRead ∧
      Cont regseqRead realRead publicRead ∧ PkgSig bundle publicRead pkg

theorem UniformCauchyCriterionPublicExportSurface_route_closure [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPublicExportSurface index windows modulus tolerance tail sealRow
        transports routes provenance name regseqRead realRead publicRead bundle pkg →
      UnaryHistory regseqRead ∧ UnaryHistory realRead ∧ UnaryHistory publicRead ∧
        Cont regseqRead realRead publicRead ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro surface
  obtain ⟨packet, indexTailRegseq, tailSealReal, regseqRealPublic, publicPkg⟩ := surface
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed regseqUnary realUnary regseqRealPublic
  exact ⟨regseqUnary, realUnary, publicUnary, regseqRealPublic, publicPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
