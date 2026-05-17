import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_phase_real_endpoint_determinacy [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name selectorRead
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow selectorRead ->
        Cont selectorRead sealRow endpoint ->
          Cont tail sealRow endpoint' ->
            PkgSig bundle selectorRead pkg ->
              PkgSig bundle endpoint pkg ->
                PkgSig bundle endpoint' pkg ->
                  hsame selectorRead endpoint' ∧ UnaryHistory endpoint ∧
                    UnaryHistory endpoint' ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet tailSealSelector selectorSealEndpoint tailSealEndpoint' _selectorPkg endpointPkg
    endpointPkg'
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealSelector
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed selectorUnary sealRowUnary selectorSealEndpoint
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed tailUnary sealRowUnary tailSealEndpoint'
  have sameEndpoint : hsame selectorRead endpoint' :=
    cont_deterministic tailSealSelector tailSealEndpoint'
  exact
    ⟨sameEndpoint, endpointUnary, endpointUnary', namePkg, endpointPkg, endpointPkg'⟩

end BEDC.Derived.UniformCauchyCriterionUp
