import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_threshold_seal_roundtrip [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name selectorRead
      rootRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow selectorRead ->
        Cont selectorRead index rootRead ->
          Cont rootRead sealRow endpoint ->
            PkgSig bundle selectorRead pkg ->
              PkgSig bundle rootRead pkg ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory windows ∧ UnaryHistory rootRead ∧ UnaryHistory endpoint ∧
                    Cont tail sealRow selectorRead ∧ Cont selectorRead index rootRead ∧
                      Cont rootRead sealRow endpoint ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealSelector selectorIndexRoot rootSealEndpoint _selectorPkg _rootPkg
    endpointPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealSelector
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed selectorUnary indexUnary selectorIndexRoot
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rootUnary sealRowUnary rootSealEndpoint
  exact
    ⟨windowsUnary, rootUnary, endpointUnary, tailSealSelector, selectorIndexRoot,
      rootSealEndpoint, namePkg, endpointPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
