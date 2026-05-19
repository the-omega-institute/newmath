import BEDC.Derived.RelationalFrameAuditUp.Carrier

namespace BEDC.Derived.RelationalFrameAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RelationalFrameAuditCarrier_full_packet_semantic_namecert [AskSetup]
    [PackageSetup]
    {multiHist observerA observerB request symmetry causal rate refusal transport continuation
      provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalFrameAuditCarrier multiHist observerA observerB request symmetry causal rate
        refusal transport continuation provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RelationalFrameAuditCarrier multiHist observerA observerB request symmetry causal
              rate refusal transport continuation provenance name bundle pkg ∧
            (hsame row multiHist ∨ hsame row observerA ∨ hsame row observerB ∨
              hsame row request ∨ hsame row symmetry ∨ hsame row causal ∨
                hsame row rate ∨ hsame row refusal ∨ hsame row transport ∨
                  hsame row continuation ∨ hsame row provenance ∨ hsame row name))
        (fun _row : BHist =>
          Cont multiHist request observerA ∧ Cont request observerB causal ∧
            Cont causal symmetry rate ∧ Cont transport continuation provenance ∧
              PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨multiHistUnary, observerAUnary, observerBUnary, requestUnary, symmetryUnary,
    causalUnary, rateUnary, refusalUnary, transportUnary, continuationUnary,
    provenanceUnary, nameUnary, multiHistRoute, requestRoute, rateRoute, provenanceRoute,
    provenancePkg, _semanticCert⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro multiHist
          (And.intro carrierWitness (Or.inl (hsame_refl multiHist)))
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
        intro _row _other sameRows sourceData
        cases sameRows
        exact sourceData
    }
    pattern_sound := by
      intro _row _sourceData
      exact
        ⟨multiHistRoute, requestRoute, rateRoute, provenanceRoute, provenancePkg⟩
    ledger_sound := by
      intro _row sourceData
      cases sourceData.right with
      | inl sameMultiHist =>
          exact ⟨unary_transport multiHistUnary (hsame_symm sameMultiHist), provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameObserverA =>
              exact
                ⟨unary_transport observerAUnary (hsame_symm sameObserverA), provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameObserverB =>
                  exact
                    ⟨unary_transport observerBUnary (hsame_symm sameObserverB),
                      provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameRequest =>
                      exact
                        ⟨unary_transport requestUnary (hsame_symm sameRequest),
                          provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameSymmetry =>
                          exact
                            ⟨unary_transport symmetryUnary (hsame_symm sameSymmetry),
                              provenancePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameCausal =>
                              exact
                                ⟨unary_transport causalUnary (hsame_symm sameCausal),
                                  provenancePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameRate =>
                                  exact
                                    ⟨unary_transport rateUnary (hsame_symm sameRate),
                                      provenancePkg⟩
                              | inr rest =>
                                  cases rest with
                                  | inl sameRefusal =>
                                      exact
                                        ⟨unary_transport refusalUnary (hsame_symm sameRefusal),
                                          provenancePkg⟩
                                  | inr rest =>
                                      cases rest with
                                      | inl sameTransport =>
                                          exact
                                            ⟨unary_transport transportUnary
                                                (hsame_symm sameTransport),
                                              provenancePkg⟩
                                      | inr rest =>
                                          cases rest with
                                          | inl sameContinuation =>
                                              exact
                                                ⟨unary_transport continuationUnary
                                                    (hsame_symm sameContinuation),
                                                  provenancePkg⟩
                                          | inr rest =>
                                              cases rest with
                                              | inl sameProvenance =>
                                                  exact
                                                    ⟨unary_transport provenanceUnary
                                                        (hsame_symm sameProvenance),
                                                      provenancePkg⟩
                                              | inr sameName =>
                                                  exact
                                                    ⟨unary_transport nameUnary
                                                        (hsame_symm sameName),
                                                      provenancePkg⟩
  }

end BEDC.Derived.RelationalFrameAuditUp
