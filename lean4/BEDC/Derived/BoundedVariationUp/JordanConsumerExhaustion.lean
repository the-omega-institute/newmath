import BEDC.Derived.BoundedVariationUp

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedVariationPartitionLedger_jordan_consumer_exhaustion [AskSetup] [PackageSetup]
    {interval partition edge endpoint dyadic variation refinement transport route provenance
      nameCert positiveEdge negativeEdge positiveRead negativeRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationPartitionLedger interval partition edge endpoint dyadic variation refinement
        transport route provenance nameCert bundle pkg ->
      UnaryHistory positiveEdge ->
        UnaryHistory negativeEdge ->
          Cont edge positiveEdge positiveRead ->
            Cont edge negativeEdge negativeRead ->
              Cont positiveRead negativeRead consumerRead ->
                PkgSig bundle positiveRead pkg ->
                  PkgSig bundle negativeRead pkg ->
                    PkgSig bundle consumerRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row positiveRead ∨ hsame row negativeRead ∨
                              hsame row consumerRead)
                          (fun _row : BHist =>
                            Cont edge positiveEdge positiveRead ∨
                              Cont edge negativeEdge negativeRead ∨
                                Cont positiveRead negativeRead consumerRead)
                          (fun row : BHist =>
                            PkgSig bundle consumerRead pkg ∧
                              (hsame row positiveRead ∨ hsame row negativeRead ∨
                                hsame row consumerRead))
                          hsame ∧
                        UnaryHistory positiveRead ∧ UnaryHistory negativeRead ∧
                          UnaryHistory consumerRead ∧ hsame variation (append edge refinement) ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle positiveRead pkg ∧
                              PkgSig bundle negativeRead pkg ∧
                                PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory SemanticNameCert
  intro ledger positiveEdgeUnary negativeEdgeUnary positiveReadRoute negativeReadRoute
    consumerReadRoute positivePkg negativePkg consumerPkg
  obtain ⟨_intervalUnary, _partitionUnary, edgeUnary, _endpointUnary, _dyadicUnary,
    _variationUnary, _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _intervalPartitionEndpoint, _endpointDyadicEdge, _edgeRefinementVariation,
    _variationTransportRoute, _routeProvenanceNameCert, variationSameAppend, provenancePkg⟩ :=
      ledger
  have positiveReadUnary : UnaryHistory positiveRead :=
    unary_cont_closed edgeUnary positiveEdgeUnary positiveReadRoute
  have negativeReadUnary : UnaryHistory negativeRead :=
    unary_cont_closed edgeUnary negativeEdgeUnary negativeReadRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed positiveReadUnary negativeReadUnary consumerReadRoute
  have sourcePositive :
      (fun row : BHist =>
        hsame row positiveRead ∨ hsame row negativeRead ∨ hsame row consumerRead)
        positiveRead :=
    Or.inl (hsame_refl positiveRead)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row positiveRead ∨ hsame row negativeRead ∨ hsame row consumerRead)
        (fun _row : BHist =>
          Cont edge positiveEdge positiveRead ∨ Cont edge negativeEdge negativeRead ∨
            Cont positiveRead negativeRead consumerRead)
        (fun row : BHist =>
          PkgSig bundle consumerRead pkg ∧
            (hsame row positiveRead ∨ hsame row negativeRead ∨ hsame row consumerRead))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro positiveRead sourcePositive
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
        cases source with
        | inl samePositive =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) samePositive)
        | inr rest =>
            cases rest with
            | inl sameNegative =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNegative))
            | inr sameConsumer =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameConsumer))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl _samePositive =>
          exact Or.inl positiveReadRoute
      | inr rest =>
          cases rest with
          | inl _sameNegative =>
              exact Or.inr (Or.inl negativeReadRoute)
          | inr _sameConsumer =>
              exact Or.inr (Or.inr consumerReadRoute)
    ledger_sound := by
      intro _row source
      exact ⟨consumerPkg, source⟩
  }
  exact
    ⟨cert, positiveReadUnary, negativeReadUnary, consumerReadUnary, variationSameAppend,
      provenancePkg, positivePkg, negativePkg, consumerPkg⟩

end BEDC.Derived.BoundedVariationUp
