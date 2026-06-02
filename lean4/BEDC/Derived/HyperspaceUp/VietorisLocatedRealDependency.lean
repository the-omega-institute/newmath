import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisLocatedRealDependency [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead hitRead symmetricRead
      locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont subsetRead netRead hitRead →
            Cont D0 D1 symmetricRead →
              Cont hitRead R locatedRead →
                Cont locatedRead symmetricRead C →
                  PkgSig bundle locatedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                            hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨
                              hsame row R ∨ hsame row locatedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle locatedRead pkg)
                        hsame ∧
                      UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                        UnaryHistory hitRead ∧ UnaryHistory symmetricRead ∧
                          UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier subsetRoute netRoute hitRoute symmetricRoute locatedRoute _hausdorffRoute
    locatedPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
    _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed subsetUnary netUnary hitRoute
  have symmetricUnary : UnaryHistory symmetricRead :=
    unary_cont_closed d0Unary d1Unary symmetricRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed hitUnary rUnary locatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row locatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle locatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro locatedRead ⟨hsame_refl locatedRead, locatedUnary⟩
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
                    (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, locatedPkg⟩
  }
  exact ⟨cert, subsetUnary, netUnary, hitUnary, symmetricUnary, locatedUnary⟩

end BEDC.Derived.HyperspaceUp
