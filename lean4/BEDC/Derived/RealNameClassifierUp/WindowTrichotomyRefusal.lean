import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierWindowTrichotomyRefusal [AskSetup] [PackageSetup]
    {sourceA sourceB window dyadicA dyadicB classifier readbackA readbackB transport replay
      provenance sealRow localName trichotomyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RealNameClassifierUp sourceA window readbackA dyadicA classifier readbackB
        sealRow transport replay provenance localName bundle pkg →
      Cont window dyadicA trichotomyRead →
        PkgSig bundle trichotomyRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row window ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
                  hsame row classifier ∨ hsame row trichotomyRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row sourceA ∨ hsame row sourceB ∨ hsame row window ∨
                  hsame row dyadicA ∨ hsame row dyadicB ∨ hsame row classifier ∨
                    hsame row trichotomyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont window dyadicA trichotomyRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle trichotomyRead pkg)
              hsame ∧
            UnaryHistory trichotomyRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier trichotomyRoute trichotomyPkg
  obtain ⟨_sourceUnary, windowUnary, _readbackAUnary, dyadicAUnary, _classifierUnary,
    _readbackBUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceWindowReplay, _readbackDyadicClassifier,
    _classifierReadbackSeal, _transportReplay, provenancePkg, _localNamePkg⟩ := carrier
  have trichotomyUnary : UnaryHistory trichotomyRead :=
    unary_cont_closed windowUnary dyadicAUnary trichotomyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row window ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
              hsame row classifier ∨ hsame row trichotomyRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row sourceB ∨ hsame row window ∨ hsame row dyadicA ∨
              hsame row dyadicB ∨ hsame row classifier ∨ hsame row trichotomyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window dyadicA trichotomyRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle trichotomyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro trichotomyRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl trichotomyRead)))),
            trichotomyUnary⟩
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
        constructor
        · cases source.left with
          | inl sameWindow =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)
          | inr rest =>
              cases rest with
              | inl sameDyadicA =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadicA))
              | inr rest =>
                  cases rest with
                  | inl sameDyadicB =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadicB)))
                  | inr rest =>
                      cases rest with
                      | inl sameClassifier =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameClassifier))))
                      | inr sameTrichotomy =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (hsame_trans (hsame_symm sameRows)
                                      sameTrichotomy))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameWindow =>
          exact Or.inr (Or.inr (Or.inl sameWindow))
      | inr rest =>
          cases rest with
          | inl sameDyadicA =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadicA)))
          | inr rest =>
              cases rest with
              | inl sameDyadicB =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDyadicB))))
              | inr rest =>
                  cases rest with
                  | inl sameClassifier =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl sameClassifier)))))
                  | inr sameTrichotomy =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr sameTrichotomy)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, trichotomyRoute, provenancePkg, trichotomyPkg⟩
  }
  exact ⟨cert, trichotomyUnary⟩

end BEDC.Derived.RealNameClassifierUp
