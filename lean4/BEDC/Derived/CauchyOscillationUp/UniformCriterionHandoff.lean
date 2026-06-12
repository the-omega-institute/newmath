import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationUniformCriterionHandoff [AskSetup] [PackageSetup]
    {W M Q T S H C P N windowRead criterionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M windowRead ->
        Cont windowRead Q criterionRead ->
          Cont criterionRead S sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row windowRead ∨ hsame row criterionRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row windowRead ∨ hsame row criterionRead ∨
                          hsame row sealRead)
                  (fun row : BHist =>
                    PkgSig bundle sealRead pkg ∧
                      (hsame row windowRead ∨ hsame row criterionRead ∨
                        hsame row sealRead))
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory criterionRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier windowRoute criterionRoute sealRoute sealPkg
  obtain ⟨wUnary, mUnary, qUnary, _tUnary, sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _wmq, _mqt, _tsc, _cnp, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary mUnary windowRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed windowUnary qUnary criterionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed criterionUnary sUnary sealRoute
  have sourceWindow :
      (fun row : BHist =>
        hsame row windowRead ∨ hsame row criterionRead ∨ hsame row sealRead)
        windowRead := by
    exact Or.inl (hsame_refl windowRead)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row windowRead ∨ hsame row criterionRead ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row windowRead ∨ hsame row criterionRead ∨ hsame row sealRead)
          (fun row : BHist =>
            PkgSig bundle sealRead pkg ∧
              (hsame row windowRead ∨ hsame row criterionRead ∨ hsame row sealRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro windowRead sourceWindow
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
        cases source with
        | inl sameWindow =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)
        | inr rest =>
            cases rest with
            | inl sameCriterion =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameCriterion))
            | inr sameSeal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameWindow =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameWindow))))))))
      | inr rest =>
          cases rest with
          | inl sameCriterion =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr (Or.inl sameCriterion)))))))))
          | inr sameSeal =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSeal)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨sealPkg, source⟩
  }
  exact ⟨cert, windowUnary, criterionUnary, sealUnary⟩

end BEDC.Derived.CauchyOscillationUp
