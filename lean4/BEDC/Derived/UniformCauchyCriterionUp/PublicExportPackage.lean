import BEDC.Derived.UniformCauchyCriterionUp.PublicExportSurface

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPublicExportSurface_package_closure [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPublicExportSurface index windows modulus tolerance tail sealRow
        transports routes provenance name regseqRead realRead publicRead bundle pkg →
      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
        UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
          UnaryHistory publicRead ∧ Cont index windows modulus ∧
            Cont modulus tolerance tail ∧ Cont index tail regseqRead ∧
              Cont tail sealRow realRead ∧ Cont regseqRead realRead publicRead ∧
                PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro surface
  obtain ⟨packet, indexTailRegseq, tailSealReal, regseqRealPublic, publicPkg⟩ := surface
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed regseqUnary realUnary regseqRealPublic
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      publicUnary, indexWindowsModulus, modulusToleranceTail, indexTailRegseq, tailSealReal,
      regseqRealPublic, namePkg, publicPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
