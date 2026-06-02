import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Hyperspace_compact_source_scope [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead netRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont X K0 compactRead ->
        Cont K0 K1 netRead ->
          Cont compactRead M completionRead ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row compactRead ∨ hsame row completionRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                      hsame row N1 ∨ hsame row M ∨ hsame row compactRead ∨
                        hsame row netRead ∨ hsame row completionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory netRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier compactRoute netRoute completionRoute completionPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed k0Unary k1Unary netRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed compactUnary mUnary completionRoute
  have sourceCompletion :
      (fun row : BHist =>
        (hsame row compactRead ∨ hsame row completionRead) ∧ UnaryHistory row)
        completionRead := by
    exact ⟨Or.inr (hsame_refl completionRead), completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compactRead ∨ hsame row completionRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row M ∨ hsame row compactRead ∨
                hsame row netRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
          | inl sameCompact =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCompact)
          | inr sameCompletion =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompact =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameCompact))))))
      | inr sameCompletion =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameCompletion)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, compactUnary, netUnary, completionUnary⟩

end BEDC.Derived.HyperspaceUp
