import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCompactCompleteHandoff [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead leftNet rightNet directedRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont X M compactRead →
        Cont K0 N0 leftNet →
          Cont K1 N1 rightNet →
            Cont D0 D1 directedRead →
              Cont compactRead directedRead handoffRead →
                PkgSig bundle handoffRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row compactRead ∨ hsame row handoffRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                          hsame row N0 ∨ hsame row N1 ∨ hsame row D0 ∨
                            hsame row D1 ∨ hsame row M ∨ hsame row compactRead ∨
                              hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle handoffRead pkg)
                      hsame ∧
                    UnaryHistory compactRead ∧ UnaryHistory leftNet ∧
                      UnaryHistory rightNet ∧ UnaryHistory directedRead ∧
                        UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont PkgSig SemanticNameCert hsame
  intro carrier compactRoute leftRoute rightRoute directedRoute handoffRoute handoffPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    _rUnary, _hsUnary, _cUnary, _provenanceUnary, mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary mUnary compactRoute
  have leftUnary : UnaryHistory leftNet :=
    unary_cont_closed k0Unary n0Unary leftRoute
  have rightUnary : UnaryHistory rightNet :=
    unary_cont_closed k1Unary n1Unary rightRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed d0Unary d1Unary directedRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed compactUnary directedUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compactRead ∨ hsame row handoffRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row M ∨
                hsame row compactRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead
          ⟨Or.inr (hsame_refl handoffRead), handoffUnary⟩
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
        intro _row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameCompact =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameCompact), otherUnary⟩
        | inr sameHandoff =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameHandoff), otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompact =>
          right
          right
          right
          right
          right
          right
          right
          right
          left
          exact sameCompact
      | inr sameHandoff =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact sameHandoff
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, compactUnary, leftUnary, rightUnary, directedUnary, handoffUnary⟩

end BEDC.Derived.HyperspaceUp
