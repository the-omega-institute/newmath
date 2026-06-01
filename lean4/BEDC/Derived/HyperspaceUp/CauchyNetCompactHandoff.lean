import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCauchyNetCompactHandoff [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M netRead cauchyRead compactRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 netRead →
        Cont netRead D0 cauchyRead →
          Cont cauchyRead R compactRead →
            Cont compactRead M namedRead →
              PkgSig bundle P pkg →
                PkgSig bundle M pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K0 ∨ hsame row K1 ∨ hsame row D0 ∨
                          hsame row R ∨ hsame row M ∨ hsame row netRead ∨
                            hsame row cauchyRead ∨ hsame row compactRead ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K0 K1 netRead ∧
                          Cont netRead D0 cauchyRead ∧
                            Cont cauchyRead R compactRead ∧
                              Cont compactRead M namedRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
                      hsame ∧
                    UnaryHistory netRead ∧ UnaryHistory cauchyRead ∧
                      UnaryHistory compactRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier netRoute cauchyRoute compactRoute namedRoute provenancePkg namePkg
  obtain ⟨_xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, d0Unary, _d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, mUnary, _carrierPkg⟩ := carrier
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed k0Unary k1Unary netRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed netUnary d0Unary cauchyRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed cauchyUnary rUnary compactRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed compactUnary mUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K0 ∨ hsame row K1 ∨ hsame row D0 ∨ hsame row R ∨
              hsame row M ∨ hsame row netRead ∨ hsame row cauchyRead ∨
                hsame row compactRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K0 K1 netRead ∧ Cont netRead D0 cauchyRead ∧
              Cont cauchyRead R compactRead ∧ Cont compactRead M namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, netRoute, cauchyRoute, compactRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, netUnary, cauchyUnary, compactUnary, namedUnary⟩

end BEDC.Derived.HyperspaceUp
