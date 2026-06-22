import BEDC.Derived.ArchimedeanOrderedFieldUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArchimedeanOrderedFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArchimedeanOrderedFieldCarrier [AskSetup] [PackageSetup]
    (real alg rat bound ledger _transport route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory real ∧ UnaryHistory alg ∧ UnaryHistory rat ∧ UnaryHistory bound ∧
    UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
      Cont real alg ledger ∧ Cont ledger bound route ∧
        Cont route provenance localCert ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localCert pkg

theorem ArchimedeanOrderedFieldNameCertObligations [AskSetup] [PackageSetup]
    {real alg rat bound ledger transport route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
        localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
              localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            hsame row real ∨ hsame row alg ∨ hsame row rat ∨ hsame row bound ∨
              hsame row ledger ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
              Cont route provenance localCert ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localCert pkg)
          hsame ∧
        UnaryHistory ledger ∧ UnaryHistory route ∧ UnaryHistory localCert := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨realUnary, algUnary, ratUnary, boundUnary, ledgerUnary, provenanceUnary,
    localCertUnary, realAlgLedger, ledgerBoundRoute, routeProvenanceCert,
      provenancePkg, localCertPkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary boundUnary ledgerBoundRoute
  have localCertFromRoute : UnaryHistory localCert :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCert
  have carrierWitness :
      ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
        localCert bundle pkg := by
    exact
      ⟨realUnary, algUnary, ratUnary, boundUnary, ledgerUnary, provenanceUnary,
        localCertUnary, realAlgLedger, ledgerBoundRoute, routeProvenanceCert,
        provenancePkg, localCertPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
              localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            hsame row real ∨ hsame row alg ∨ hsame row rat ∨ hsame row bound ∨
              hsame row ledger ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
              Cont route provenance localCert ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localCert pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localCert ⟨carrierWitness, hsame_refl localCert⟩
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
          ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
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
                    (Or.inr source.right))))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport localCertFromRoute (hsame_symm source.right),
          realAlgLedger, ledgerBoundRoute, routeProvenanceCert, provenancePkg,
          localCertPkg⟩
  }
  exact ⟨cert, ledgerUnary, routeUnary, localCertFromRoute⟩

theorem ArchimedeanOrderedFieldRationalBoundWindow [AskSetup] [PackageSetup]
    {real alg rat bound ledger transport route provenance localCert comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
        localCert bundle pkg →
      Cont bound rat comparisonRead →
        PkgSig bundle comparisonRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row rat ∨ hsame row bound ∨ hsame row ledger ∨
                    hsame row comparisonRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row real ∨ hsame row rat ∨ hsame row bound ∨
                  hsame row ledger ∨ hsame row comparisonRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
                  Cont bound rat comparisonRead ∧ PkgSig bundle comparisonRead pkg)
              hsame ∧ UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier boundRatRead comparisonPkg
  obtain ⟨realUnary, algUnary, ratUnary, boundUnary, ledgerUnary, provenanceUnary,
    localCertUnary, realAlgLedger, ledgerBoundRoute, routeProvenanceCert,
      provenancePkg, localCertPkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed boundUnary ratUnary boundRatRead
  have sourceComparison :
      (hsame comparisonRead rat ∨ hsame comparisonRead bound ∨ hsame comparisonRead ledger ∨
          hsame comparisonRead comparisonRead) ∧ UnaryHistory comparisonRead :=
    ⟨Or.inr (Or.inr (Or.inr (hsame_refl comparisonRead))), comparisonUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row rat ∨ hsame row bound ∨ hsame row ledger ∨
                hsame row comparisonRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row real ∨ hsame row rat ∨ hsame row bound ∨
              hsame row ledger ∨ hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real alg ledger ∧ Cont ledger bound route ∧
              Cont bound rat comparisonRead ∧ PkgSig bundle comparisonRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead sourceComparison
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
        exact
          ⟨by
            cases source.left with
            | inl rowRat =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) rowRat)
            | inr rest =>
                cases rest with
                | inl rowBound =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowBound))
                | inr restTail =>
                    cases restTail with
                    | inl rowLedger =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) rowLedger)))
                    | inr rowComparison =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (hsame_trans (hsame_symm sameRows) rowComparison))),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      cases source.left with
      | inl rowRat => exact Or.inr (Or.inl rowRat)
      | inr rest =>
          cases rest with
          | inl rowBound => exact Or.inr (Or.inr (Or.inl rowBound))
          | inr restTail =>
              cases restTail with
              | inl rowLedger => exact Or.inr (Or.inr (Or.inr (Or.inl rowLedger)))
              | inr rowComparison =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr rowComparison)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, realAlgLedger, ledgerBoundRoute, boundRatRead, comparisonPkg⟩
  }
  exact ⟨cert, comparisonUnary⟩

end BEDC.Derived.ArchimedeanOrderedFieldUp
