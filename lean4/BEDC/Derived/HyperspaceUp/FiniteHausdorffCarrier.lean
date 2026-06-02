import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceFiniteHausdorffCarrier [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M directedLeft directedRight symmetricRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont D0 R directedLeft ->
        Cont D1 R directedRight ->
          Cont directedLeft directedRight symmetricRead ->
            PkgSig bundle symmetricRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row directedLeft ∨ hsame row directedRight ∨
                        hsame row symmetricRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                      hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                        hsame row directedLeft ∨ hsame row directedRight ∨
                          hsame row symmetricRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle symmetricRead pkg)
                  hsame ∧
                UnaryHistory directedLeft ∧ UnaryHistory directedRight ∧
                  UnaryHistory symmetricRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier directedLeftRoute directedRightRoute symmetricRoute symmetricPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have directedLeftUnary : UnaryHistory directedLeft :=
    unary_cont_closed d0Unary rUnary directedLeftRoute
  have directedRightUnary : UnaryHistory directedRight :=
    unary_cont_closed d1Unary rUnary directedRightRoute
  have symmetricUnary : UnaryHistory symmetricRead :=
    unary_cont_closed directedLeftUnary directedRightUnary symmetricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row directedLeft ∨ hsame row directedRight ∨ hsame row symmetricRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row directedLeft ∨ hsame row directedRight ∨
                  hsame row symmetricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle symmetricRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro symmetricRead
          ⟨Or.inr (Or.inr (hsame_refl symmetricRead)), symmetricUnary⟩
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
          | inl leftSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) leftSame)
          | inr rest =>
              cases rest with
              | inl rightSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rightSame))
              | inr symmetricSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) symmetricSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl leftSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl leftSame))))))))
      | inr rest =>
          cases rest with
          | inl rightSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inl rightSame)))))))))
          | inr symmetricSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr symmetricSame)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, symmetricPkg⟩
  }
  exact ⟨cert, directedLeftUnary, directedRightUnary, symmetricUnary⟩

end BEDC.Derived.HyperspaceUp
