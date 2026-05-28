import BEDC.Derived.BoundedVariationUp

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedVariationCarrier_real_dependency_scope [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      endpointRead realRead dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont interval partition endpointRead ->
        Cont endpointRead endpoint realRead ->
          Cont realRead dyadic dyadicRead ->
            PkgSig bundle dyadicRead pkg ->
              UnaryHistory endpointRead ∧ UnaryHistory realRead ∧
                UnaryHistory dyadicRead ∧ Cont interval partition endpointRead ∧
                  Cont endpointRead endpoint realRead ∧ Cont realRead dyadic dyadicRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle dyadicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier intervalPartitionEndpointRead endpointReadEndpointRealRead
    realReadDyadicDyadicRead dyadicPkg
  obtain ⟨intervalUnary, partitionUnary, endpointUnary, dyadicUnary, _variationUnary,
    _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, _variationSame, provenancePkg⟩ :=
      carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalUnary partitionUnary intervalPartitionEndpointRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointReadUnary endpointUnary endpointReadEndpointRealRead
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed realReadUnary dyadicUnary realReadDyadicDyadicRead
  exact
    ⟨endpointReadUnary, realReadUnary, dyadicReadUnary, intervalPartitionEndpointRead,
      endpointReadEndpointRealRead, realReadDyadicDyadicRead, provenancePkg, dyadicPkg⟩

theorem BoundedVariationCarrier_public_namecert_export [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      edge ledgerEndpoint ledgerVariation ledgerRoute ledgerNameCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      BoundedVariationPartitionLedger interval partition edge ledgerEndpoint dyadic
          ledgerVariation refinement transport ledgerRoute provenance ledgerNameCert bundle pkg ->
        Cont nameCert ledgerNameCert publicRead ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row nameCert ∨ hsame row ledgerNameCert ∨
                  Cont nameCert ledgerNameCert publicRead)
              (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row publicRead)
              hsame ∧
            UnaryHistory publicRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier ledger nameLedgerPublic
  obtain ⟨_intervalUnary, _partitionUnary, _endpointUnary, _dyadicUnary, _variationUnary,
    _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, _variationSame, provenancePkg⟩ :=
      carrier
  obtain ⟨_ledgerIntervalUnary, _ledgerPartitionUnary, _edgeUnary, _ledgerEndpointUnary,
    _ledgerDyadicUnary, _ledgerVariationUnary, _ledgerRefinementUnary, _ledgerTransportUnary,
    _ledgerRouteUnary, _ledgerProvenanceUnary, ledgerNameCertUnary, _ledgerIntervalEndpoint,
    _ledgerEndpointDyadicEdge, _ledgerEdgeRefinementVariation, _ledgerVariationTransportRoute,
    _ledgerRouteProvenanceNameCert, _ledgerVariationSameAppend, _ledgerProvenancePkg⟩ :=
      ledger
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed nameCertUnary ledgerNameCertUnary nameLedgerPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nameCert ∨ hsame row ledgerNameCert ∨
              Cont nameCert ledgerNameCert publicRead)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr nameLedgerPublic)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }
  exact ⟨cert, publicReadUnary, provenancePkg⟩

end BEDC.Derived.BoundedVariationUp
