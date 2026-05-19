import BEDC.Derived.BinderContextSubstitutionSealUp

namespace BEDC.Derived.BinderContextSubstitutionSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinderContextSubstitutionSealCarrier_compiler_handoff
    [AskSetup] [PackageSetup]
    {term depth payload result boundary transport route provenance name endpoint compiled : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg ->
      Cont result boundary endpoint ->
      Cont payload endpoint compiled ->
      PkgSig bundle compiled pkg ->
        SemanticNameCert
          (fun row : BHist =>
            BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
              provenance name bundle pkg ∧ hsame row compiled)
          (fun row : BHist =>
            UnaryHistory row ∧ (hsame row result ∨ hsame row endpoint ∨ hsame row compiled))
          (fun _row : BHist =>
            Cont result boundary endpoint ∧ Cont payload endpoint compiled ∧
              PkgSig bundle result pkg ∧ PkgSig bundle compiled pkg)
          hsame ∧ hsame endpoint result ∧ UnaryHistory compiled := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier endpointRoute payloadEndpointCompiled compiledPkg
  have carrierWitness :
      BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
        provenance name bundle pkg := carrier
  obtain ⟨_termUnary, _depthUnary, payloadUnary, resultUnary, boundaryUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _termDepthResult,
    boundaryEmpty, _payloadResultTransport, _transportBoundaryRoute, _provenanceResult,
    resultPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed resultUnary boundaryUnary endpointRoute
  have endpointResult : hsame endpoint result := by
    cases boundaryEmpty
    exact cont_deterministic endpointRoute (cont_right_unit result)
  have compiledUnary : UnaryHistory compiled :=
    unary_cont_closed payloadUnary endpointUnary payloadEndpointCompiled
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          BinderContextSubstitutionSealCarrier term depth payload result boundary transport route
            provenance name bundle pkg ∧ hsame row compiled)
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row result ∨ hsame row endpoint ∨ hsame row compiled))
        (fun _row : BHist =>
          Cont result boundary endpoint ∧ Cont payload endpoint compiled ∧
            PkgSig bundle result pkg ∧ PkgSig bundle compiled pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro compiled
          ⟨carrierWitness, hsame_refl compiled⟩
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
          intro _row _other sameRows sourceRow
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨unary_transport compiledUnary (hsame_symm sourceRow.right),
            Or.inr (Or.inr sourceRow.right)⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨endpointRoute, payloadEndpointCompiled, resultPkg, compiledPkg⟩
    }
  exact ⟨cert, endpointResult, compiledUnary⟩

end BEDC.Derived.BinderContextSubstitutionSealUp
