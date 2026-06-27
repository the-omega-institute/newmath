import BEDC.Derived.CauchyCompletionMinimalityUp.RouteInduction

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityLedgerExactness [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead comparedRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg →
      Cont completion embedding denseRead →
        Cont extension separated comparedRead →
          Cont replay name nameRead →
            PkgSig bundle provenance pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                      hsame row nameRead)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
                      hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                        hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                          hsame row name ∨ hsame row nameRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont completion embedding denseRead ∧
                      Cont extension separated comparedRead ∧ Cont replay name nameRead ∧
                        PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier denseRoute comparedRoute nameRoute provenancePkg
  obtain ⟨_sourceUnary, _completionUnary, _embeddingUnary, _universalUnary, _extensionUnary,
    _separatedUnary, _transportUnary, replayUnary, provenanceUnary, nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, _carrierProvenancePkg⟩ := carrier
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed replayUnary nameUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row replay ∨ hsame row provenance ∨ hsame row name ∨ hsame row nameRead)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont extension separated comparedRead ∧ Cont replay name nameRead ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nameRead (Or.inr (Or.inr (Or.inr (hsame_refl nameRead))))
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
        intro row other sameRows source
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        cases source with
        | inl sameReplay =>
            exact Or.inl (lift sameReplay)
        | inr tail =>
            cases tail with
            | inl sameProvenance =>
                exact Or.inr (Or.inl (lift sameProvenance))
            | inr tail =>
                cases tail with
                | inl sameName =>
                    exact Or.inr (Or.inr (Or.inl (lift sameName)))
                | inr sameNameRead =>
                    exact Or.inr (Or.inr (Or.inr (lift sameNameRead)))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameReplay =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameReplay)))))))
      | inr tail =>
          cases tail with
          | inl sameProvenance =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameProvenance))))))))
          | inr tail =>
              cases tail with
              | inl sameName =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inr (Or.inl sameName)))))))))
              | inr sameNameRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (Or.inr (Or.inr sameNameRead)))))))))
    ledger_sound := by
      intro _row source
      have rowUnary : UnaryHistory _row := by
        cases source with
        | inl sameReplay =>
            exact unary_transport_symm replayUnary sameReplay
        | inr tail =>
            cases tail with
            | inl sameProvenance =>
                exact unary_transport_symm provenanceUnary sameProvenance
            | inr tail =>
                cases tail with
                | inl sameName =>
                    exact unary_transport_symm nameUnary sameName
                | inr sameNameRead =>
                    exact unary_transport_symm nameReadUnary sameNameRead
      exact ⟨rowUnary, denseRoute, comparedRoute, nameRoute, provenancePkg⟩
  }
  exact ⟨cert, nameReadUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
