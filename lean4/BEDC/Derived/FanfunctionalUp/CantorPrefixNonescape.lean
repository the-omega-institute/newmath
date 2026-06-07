import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalCantorPrefixNonescape [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead barRead windowRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg ->
      Cont C F prefixRead ->
        Cont prefixRead B barRead ->
          Cont barRead W windowRead ->
            Cont windowRead N namedRead ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row F ∨ hsame row B ∨ hsame row W ∨
                        hsame row M ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                          hsame row N ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C F prefixRead ∧
                        Cont prefixRead B barRead ∧ Cont barRead W windowRead ∧
                          Cont windowRead N namedRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory prefixRead ∧ UnaryHistory barRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute barRoute windowRoute namedRoute namedPkg
  obtain ⟨cUnary, fUnary, _epsUnary, bUnary, _dUnary, wUnary, _mUnary, _hUnary,
    _kUnary, _pUnary, nUnary, _transportLocalName, _branchDepthWitness,
    _witnessModulusReplay, provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary fUnary prefixRoute
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed prefixUnary bUnary barRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed barUnary wUnary windowRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed windowUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row F ∨ hsame row B ∨ hsame row W ∨ hsame row M ∨
              hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C F prefixRead ∧ Cont prefixRead B barRead ∧
              Cont barRead W windowRead ∧ Cont windowRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, barRoute, windowRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, prefixUnary, barUnary, windowUnary, namedUnary⟩

end BEDC.Derived.FanfunctionalUp
