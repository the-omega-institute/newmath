import BEDC.Derived.CauchyCompletionMinimalityUp.UniversalFactorization

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityCarrier_finite_row_induction [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead universalRead extensionRead comparedRead replayRead provenanceRead
      nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg →
      Cont completion embedding denseRead →
        Cont denseRead universal universalRead →
          Cont universalRead extension extensionRead →
            Cont extension separated comparedRead →
              Cont comparedRead replay replayRead →
                Cont replayRead provenance provenanceRead →
                  Cont provenanceRead name nameRead →
                    PkgSig bundle name pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
                              hsame row universal ∨ hsame row extension ∨
                                hsame row separated ∨ hsame row transport ∨
                                  hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                                    hsame row nameRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont completion embedding denseRead ∧
                              Cont denseRead universal universalRead ∧
                                Cont universalRead extension extensionRead ∧
                                  Cont extension separated comparedRead ∧
                                    Cont comparedRead replay replayRead ∧
                                      Cont replayRead provenance provenanceRead ∧
                                        Cont provenanceRead name nameRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle name pkg)
                          hsame ∧
                        UnaryHistory denseRead ∧ UnaryHistory universalRead ∧
                          UnaryHistory extensionRead ∧ UnaryHistory comparedRead ∧
                            UnaryHistory replayRead ∧ UnaryHistory provenanceRead ∧
                              UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier denseRoute universalRoute extensionRoute comparedRoute replayRoute
    provenanceRoute nameRoute namePkg
  obtain ⟨_sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed denseUnary universalUnary universalRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed universalReadUnary extensionUnary extensionRoute
  have comparedUnary : UnaryHistory comparedRead :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed comparedUnary replayUnary replayRoute
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayReadUnary provenanceUnary provenanceRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed provenanceReadUnary nameUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont denseRead universal universalRead ∧
                Cont universalRead extension extensionRead ∧
                  Cont extension separated comparedRead ∧
                    Cont comparedRead replay replayRead ∧
                      Cont replayRead provenance provenanceRead ∧
                        Cont provenanceRead name nameRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameReadUnary⟩
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
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, universalRoute, extensionRoute, comparedRoute,
          replayRoute, provenanceRoute, nameRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, denseUnary, universalReadUnary, extensionReadUnary, comparedUnary,
      replayReadUnary, provenanceReadUnary, nameReadUnary⟩

theorem CauchyCompletionMinimalityCarrier_transport_stability [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      source' completion' embedding' universal' extension' separated' transport' replay'
      provenance' name' denseRead comparedRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg →
      CauchyCompletionMinimalityCarrier source' completion' embedding' universal' extension'
          separated' transport' replay' provenance' name' bundle pkg →
        hsame completion completion' →
          hsame embedding embedding' →
            hsame extension extension' →
              hsame separated separated' →
                Cont completion embedding denseRead →
                  Cont extension separated comparedRead →
                    Cont completion' embedding' transportedRead →
                      SemanticNameCert
                          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row denseRead ∨ hsame row comparedRead ∨
                              hsame row transportedRead ∨ hsame row transport ∨
                                hsame row transport')
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont completion embedding denseRead ∧
                              Cont extension separated comparedRead ∧
                                Cont completion' embedding' transportedRead ∧
                                  hsame completion completion' ∧
                                    hsame embedding embedding' ∧
                                      hsame extension extension' ∧
                                        hsame separated separated')
                          hsame ∧
                        UnaryHistory denseRead ∧ UnaryHistory comparedRead ∧
                          UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro sourceCarrier targetCarrier sameCompletion sameEmbedding sameExtension sameSeparated
    denseRoute comparedRoute transportedRoute
  obtain ⟨_sourceUnary, completionUnary, embeddingUnary, _universalUnary, extensionUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, _provenancePkg⟩ := sourceCarrier
  obtain ⟨_sourceUnary', completionUnary', embeddingUnary', _universalUnary',
    _extensionUnary', _separatedUnary', _transportUnary', _replayUnary',
    _provenanceUnary', _nameUnary', _targetUniversalRoute, _targetSeparatedRoute,
    _targetProvenancePkg⟩ := targetCarrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have comparedUnary : UnaryHistory comparedRead :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed completionUnary' embeddingUnary' transportedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row denseRead ∨ hsame row comparedRead ∨
              hsame row transportedRead ∨ hsame row transport ∨ hsame row transport')
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont extension separated comparedRead ∧
                Cont completion' embedding' transportedRead ∧
                  hsame completion completion' ∧ hsame embedding embedding' ∧
                    hsame extension extension' ∧ hsame separated separated')
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedRead ⟨hsame_refl transportedRead, transportedUnary⟩
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
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, comparedRoute, transportedRoute, sameCompletion,
          sameEmbedding, sameExtension, sameSeparated⟩
  }
  exact ⟨cert, denseUnary, comparedUnary, transportedUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
