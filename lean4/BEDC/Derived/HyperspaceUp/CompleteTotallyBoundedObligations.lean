import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCompleteTotallyBoundedObligations [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead leftNet rightNet directedRead
      toleranceRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont X M compactRead →
        Cont K0 N0 leftNet →
          Cont K1 N1 rightNet →
            Cont D0 D1 directedRead →
              Cont directedRead R toleranceRead →
                Cont Hs C replayRead →
                  PkgSig bundle toleranceRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          (hsame row compactRead ∨ hsame row leftNet ∨
                            hsame row rightNet ∨ hsame row directedRead ∨
                              hsame row toleranceRead ∨ hsame row replayRead) ∧
                            UnaryHistory row)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                            hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                              hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                                hsame row compactRead ∨ hsame row leftNet ∨
                                  hsame row rightNet ∨ hsame row directedRead ∨
                                    hsame row toleranceRead ∨ hsame row replayRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle toleranceRead pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory leftNet ∧
                        UnaryHistory rightNet ∧ UnaryHistory directedRead ∧
                          UnaryHistory toleranceRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier compactRoute leftRoute rightRoute directedRoute toleranceRoute replayRoute
    tolerancePkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
    hsUnary, cUnary, _pUnary, mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary mUnary compactRoute
  have leftNetUnary : UnaryHistory leftNet :=
    unary_cont_closed k0Unary n0Unary leftRoute
  have rightNetUnary : UnaryHistory rightNet :=
    unary_cont_closed k1Unary n1Unary rightRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed d0Unary d1Unary directedRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed directedUnary rUnary toleranceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compactRead ∨ hsame row leftNet ∨ hsame row rightNet ∨
              hsame row directedRead ∨ hsame row toleranceRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                  hsame row compactRead ∨ hsame row leftNet ∨ hsame row rightNet ∨
                    hsame row directedRead ∨ hsame row toleranceRead ∨
                      hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle toleranceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro toleranceRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl toleranceRead))))),
            toleranceUnary⟩
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
          | inr rest =>
              cases rest with
              | inl sameLeft =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLeft))
              | inr rest =>
                  cases rest with
                  | inl sameRight =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRight)))
                  | inr rest =>
                      cases rest with
                      | inl sameDirected =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameDirected))))
                      | inr rest =>
                          cases rest with
                          | inl sameTolerance =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans
                                            (hsame_symm sameRows) sameTolerance)))))
                          | inr sameReplay =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm sameRows) sameReplay)))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompact =>
          right; right; right; right; right; right
          right; right; right; right; right; right
          exact Or.inl sameCompact
      | inr rest =>
          cases rest with
          | inl sameLeft =>
              right; right; right; right; right; right
              right; right; right; right; right; right
              right
              exact Or.inl sameLeft
          | inr rest =>
              cases rest with
              | inl sameRight =>
                  right; right; right; right; right; right
                  right; right; right; right; right; right
                  right; right
                  exact Or.inl sameRight
              | inr rest =>
                  cases rest with
                  | inl sameDirected =>
                      right; right; right; right; right; right
                      right; right; right; right; right; right
                      right; right; right
                      exact Or.inl sameDirected
                  | inr rest =>
                      cases rest with
                      | inl sameTolerance =>
                          right; right; right; right; right; right
                          right; right; right; right; right; right
                          right; right; right; right
                          exact Or.inl sameTolerance
                      | inr sameReplay =>
                          right; right; right; right; right; right
                          right; right; right; right; right; right
                          right; right; right; right; right
                          exact sameReplay
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, tolerancePkg⟩
  }
  exact
    ⟨cert, compactUnary, leftNetUnary, rightNetUnary, directedUnary, toleranceUnary,
      replayUnary⟩

end BEDC.Derived.HyperspaceUp
