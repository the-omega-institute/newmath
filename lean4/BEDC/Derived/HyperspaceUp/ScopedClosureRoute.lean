import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceScopedClosureRoute [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead hausdorffRead vietorisRead
      completionRead replayRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont X K0 compactRead ->
        Cont D0 D1 hausdorffRead ->
          Cont N0 N1 vietorisRead ->
            Cont compactRead M completionRead ->
              Cont Hs C replayRead ->
                Cont replayRead M localRead ->
                  PkgSig bundle completionRead pkg ->
                    PkgSig bundle localRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row compactRead ∨ hsame row hausdorffRead ∨
                              hsame row vietorisRead ∨ hsame row completionRead ∨
                                hsame row localRead) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                              hsame row N0 ∨ hsame row N1 ∨ hsame row D0 ∨
                                hsame row D1 ∨ hsame row R ∨ hsame row Hs ∨
                                  hsame row C ∨ hsame row P ∨ hsame row M ∨
                                    hsame row compactRead ∨ hsame row hausdorffRead ∨
                                      hsame row vietorisRead ∨ hsame row completionRead ∨
                                        hsame row replayRead ∨ hsame row localRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              (PkgSig bundle completionRead pkg ∨
                                PkgSig bundle localRead pkg))
                          hsame ∧
                        UnaryHistory compactRead ∧ UnaryHistory hausdorffRead ∧
                          UnaryHistory vietorisRead ∧ UnaryHistory completionRead ∧
                            UnaryHistory replayRead ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier compactRoute hausdorffRoute vietorisRoute completionRoute replayRoute
    localRoute completionPkg localPkg
  obtain ⟨xUnary, k0Unary, _k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    _rUnary, hsUnary, cUnary, _pUnary, mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed d0Unary d1Unary hausdorffRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed n0Unary n1Unary vietorisRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed compactUnary mUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed replayUnary mUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compactRead ∨ hsame row hausdorffRead ∨ hsame row vietorisRead ∨
              hsame row completionRead ∨ hsame row localRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                  hsame row compactRead ∨ hsame row hausdorffRead ∨
                    hsame row vietorisRead ∨ hsame row completionRead ∨
                      hsame row replayRead ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧
              (PkgSig bundle completionRead pkg ∨ PkgSig bundle localRead pkg))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl completionRead)))),
            completionUnary⟩
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
        cases source.left with
        | inl sameCompact =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameCompact),
                unary_transport source.right sameRows⟩
        | inr rest =>
            cases rest with
            | inl sameHausdorff =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameHausdorff)),
                    unary_transport source.right sameRows⟩
            | inr rest =>
                cases rest with
                | inl sameVietoris =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameVietoris))),
                        unary_transport source.right sameRows⟩
                | inr rest =>
                    cases rest with
                    | inl sameCompletion =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameCompletion)))),
                            unary_transport source.right sameRows⟩
                    | inr sameLocal =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (hsame_trans (hsame_symm sameRows) sameLocal)))),
                            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompact =>
          right; right; right; right; right; right; right; right; right; right; right; right
          exact Or.inl sameCompact
      | inr rest =>
          cases rest with
          | inl sameHausdorff =>
              right; right; right; right; right; right; right; right; right; right; right
              right; right
              exact Or.inl sameHausdorff
          | inr rest =>
              cases rest with
              | inl sameVietoris =>
                  right; right; right; right; right; right; right; right; right; right; right
                  right; right; right
                  exact Or.inl sameVietoris
              | inr rest =>
                  cases rest with
                  | inl sameCompletion =>
                      right; right; right; right; right; right; right; right; right; right
                      right; right; right; right; right
                      exact Or.inl sameCompletion
                  | inr sameLocal =>
                      right; right; right; right; right; right; right; right; right; right
                      right; right; right; right; right; right; right
                      exact sameLocal
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl _sameCompact =>
          exact ⟨source.right, provenancePkg, Or.inl completionPkg⟩
      | inr rest =>
          cases rest with
          | inl _sameHausdorff =>
              exact ⟨source.right, provenancePkg, Or.inl completionPkg⟩
          | inr rest =>
              cases rest with
              | inl _sameVietoris =>
                  exact ⟨source.right, provenancePkg, Or.inl completionPkg⟩
              | inr rest =>
                  cases rest with
                  | inl _sameCompletion =>
                      exact ⟨source.right, provenancePkg, Or.inl completionPkg⟩
                  | inr _sameLocal =>
                      exact ⟨source.right, provenancePkg, Or.inr localPkg⟩
  }
  exact
    ⟨cert, compactUnary, hausdorffUnary, vietorisUnary, completionUnary, replayUnary,
      localUnary⟩

end BEDC.Derived.HyperspaceUp
