import BEDC.Derived.CauchyCompletionMinimalityUp.LedgerExactness

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityBridgeBoundary [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead universalRead extensionRead comparedRead replayRead provenanceRead nameRead
      bridgeRead : BHist}
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
                    Cont nameRead transport bridgeRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle name pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row source ∨ hsame row completion ∨
                                  hsame row embedding ∨ hsame row universal ∨
                                    hsame row extension ∨ hsame row separated ∨
                                      hsame row replay ∨ hsame row provenance ∨
                                        hsame row name ∨ hsame row bridgeRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont nameRead transport bridgeRead ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
                              hsame ∧
                            UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: CauchyCompletionMinimalityCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute universalRoute extensionRoute comparedRoute replayRoute
    provenanceRoute nameRoute bridgeRoute provenancePkg namePkg
  obtain ⟨_sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, transportUnary, replayUnary, provenanceUnary, nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, _carrierProvenancePkg⟩ := carrier
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
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed nameReadUnary transportUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont nameRead transport bridgeRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, bridgeReadUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
