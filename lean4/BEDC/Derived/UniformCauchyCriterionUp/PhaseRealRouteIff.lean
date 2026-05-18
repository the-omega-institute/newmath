import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_phase_real_route_iff [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead consumer selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      PkgSig bundle tailRead pkg ->
        PkgSig bundle sealRead pkg ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle selectorRead pkg ->
              ((Cont index tail tailRead ∧ Cont tail sealRow sealRead ∧
                    Cont tailRead sealRead consumer ∧ Cont consumer provenance selectorRead) ↔
                (UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ UnaryHistory consumer ∧
                  UnaryHistory selectorRead ∧ Cont index tail tailRead ∧
                    Cont tail sealRow sealRead ∧ Cont tailRead sealRead consumer ∧
                      Cont consumer provenance selectorRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle tailRead pkg ∧ PkgSig bundle sealRead pkg ∧
                          PkgSig bundle consumer pkg ∧
                            PkgSig bundle selectorRead pkg)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet tailPkg sealPkg consumerPkg selectorPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealUnary, _transportsUnary, _routesUnary, provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  constructor
  · intro route
    obtain ⟨indexTail, tailSeal, tailSealConsumer, consumerProvenanceSelector⟩ := route
    have tailReadUnary : UnaryHistory tailRead :=
      unary_cont_closed indexUnary tailUnary indexTail
    have sealReadUnary : UnaryHistory sealRead :=
      unary_cont_closed tailUnary sealUnary tailSeal
    have consumerUnary : UnaryHistory consumer :=
      unary_cont_closed tailReadUnary sealReadUnary tailSealConsumer
    have selectorUnary : UnaryHistory selectorRead :=
      unary_cont_closed consumerUnary provenanceUnary consumerProvenanceSelector
    exact
      ⟨tailReadUnary, sealReadUnary, consumerUnary, selectorUnary, indexTail, tailSeal,
        tailSealConsumer, consumerProvenanceSelector, namePkg, tailPkg, sealPkg,
        consumerPkg, selectorPkg⟩
  · intro packaged
    obtain
      ⟨_tailReadUnary, _sealReadUnary, _consumerUnary, _selectorUnary, indexTail, tailSeal,
        tailSealConsumer, consumerProvenanceSelector, _namePkg, _tailPkg, _sealPkg,
        _consumerPkg, _selectorPkg⟩ := packaged
    exact ⟨indexTail, tailSeal, tailSealConsumer, consumerProvenanceSelector⟩

end BEDC.Derived.UniformCauchyCriterionUp
