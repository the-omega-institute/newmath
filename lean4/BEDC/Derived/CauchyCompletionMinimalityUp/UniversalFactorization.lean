import BEDC.Derived.CauchyCompletionMinimalityUp.DenseImageCoverage

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityCarrier_universal_factorization [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead universalRead extensionRead compared : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg ->
      Cont completion embedding denseRead ->
        Cont denseRead universal universalRead ->
          Cont universalRead extension extensionRead ->
            Cont extension separated compared ->
              PkgSig bundle name pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row compared ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
                        hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                          hsame row compared)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont completion embedding denseRead ∧
                        Cont denseRead universal universalRead ∧
                          Cont universalRead extension extensionRead ∧
                            Cont extension separated compared ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle name pkg)
                    hsame ∧
                  UnaryHistory denseRead ∧ UnaryHistory universalRead ∧
                    UnaryHistory extensionRead ∧ UnaryHistory compared := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute universalRoute extensionRoute comparedRoute namePkg
  obtain ⟨sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed denseUnary universalUnary universalRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed universalReadUnary extensionUnary extensionRoute
  have comparedUnary : UnaryHistory compared :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compared ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row compared)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont denseRead universal universalRead ∧ Cont universalRead extension extensionRead ∧
                Cont extension separated compared ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compared ⟨hsame_refl compared, comparedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, universalRoute, extensionRoute, comparedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, denseUnary, universalReadUnary, extensionReadUnary, comparedUnary⟩

theorem CauchyCompletionMinimalityReplayNonescape [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead universalRead extensionRead comparedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg ->
      Cont completion embedding denseRead ->
        Cont denseRead universal universalRead ->
          Cont universalRead extension extensionRead ->
            Cont extension separated comparedRead ->
              Cont comparedRead replay replayRead ->
                PkgSig bundle name pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
                          hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                            hsame row replay ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont completion embedding denseRead ∧
                          Cont denseRead universal universalRead ∧
                            Cont universalRead extension extensionRead ∧
                              Cont extension separated comparedRead ∧
                                Cont comparedRead replay replayRead ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
                      hsame ∧
                    UnaryHistory denseRead ∧ UnaryHistory universalRead ∧
                      UnaryHistory extensionRead ∧ UnaryHistory comparedRead ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute universalRoute extensionRoute comparedRoute replayRoute namePkg
  obtain ⟨_sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row replay ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont denseRead universal universalRead ∧ Cont universalRead extension extensionRead ∧
                Cont extension separated comparedRead ∧ Cont comparedRead replay replayRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
              (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, universalRoute, extensionRoute, comparedRoute,
          replayRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, denseUnary, universalReadUnary, extensionReadUnary, comparedUnary,
      replayReadUnary⟩


theorem CauchyCompletionMinimalityReflectorUnitFactorization [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      unitRead denseRead universalRead extensionRead compared : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg ->
      Cont source completion unitRead ->
        Cont unitRead embedding denseRead ->
          Cont denseRead universal universalRead ->
            Cont universalRead extension extensionRead ->
              Cont extension separated compared ->
                PkgSig bundle provenance pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row unitRead ∨ hsame row denseRead ∨ hsame row compared) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
                          hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                            hsame row unitRead ∨ hsame row denseRead ∨ hsame row compared)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont source completion unitRead ∧
                          Cont unitRead embedding denseRead ∧
                            Cont denseRead universal universalRead ∧
                              Cont universalRead extension extensionRead ∧
                                Cont extension separated compared ∧
                                  PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory unitRead ∧ UnaryHistory denseRead ∧
                      UnaryHistory compared := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier unitRoute denseRoute universalRoute extensionRoute comparedRoute provenancePkg
  obtain ⟨sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, _carrierProvenancePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed sourceUnary completionUnary unitRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed unitUnary embeddingUnary denseRoute
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed denseUnary universalUnary universalRoute
  have _extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed universalReadUnary extensionUnary extensionRoute
  have comparedUnary : UnaryHistory compared :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row unitRead ∨ hsame row denseRead ∨ hsame row compared) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row unitRead ∨ hsame row denseRead ∨ hsame row compared)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source completion unitRead ∧
              Cont unitRead embedding denseRead ∧ Cont denseRead universal universalRead ∧
                Cont universalRead extension extensionRead ∧ Cont extension separated compared ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro unitRead
          ⟨Or.inl (hsame_refl unitRead), unitUnary⟩
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
        obtain ⟨sourceRows, sourceUnaryRow⟩ := source
        constructor
        · cases sourceRows with
          | inl unitSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) unitSame)
          | inr rest =>
              cases rest with
              | inl denseSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) denseSame))
              | inr comparedSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) comparedSame))
        · exact unary_transport sourceUnaryRow sameRows
    }
    pattern_sound := by
      intro _row source
      obtain ⟨sourceRows, _sourceUnaryRow⟩ := source
      cases sourceRows with
      | inl unitSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl unitSame))))))
      | inr rest =>
          cases rest with
          | inl denseSame =>
              exact
                Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl denseSame)))))))
          | inr comparedSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr comparedSame)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, unitRoute, denseRoute, universalRoute, extensionRoute,
          comparedRoute, provenancePkg⟩
  }
  exact ⟨cert, unitUnary, denseUnary, comparedUnary⟩


end BEDC.Derived.CauchyCompletionMinimalityUp
