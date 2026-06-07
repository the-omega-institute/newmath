import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalReadbackNonescape [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N selectorRead regularRead cofinalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont Q F selectorRead ->
        Cont selectorRead R regularRead ->
          Cont regularRead W cofinalRead ->
            PkgSig bundle cofinalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row cofinalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
                      hsame row W ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row cofinalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Q F selectorRead ∧
                      Cont selectorRead R regularRead ∧
                        Cont regularRead W cofinalRead ∧
                          PkgSig bundle cofinalRead pkg ∧ PkgSig bundle P pkg)
                  hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory regularRead ∧
                UnaryHistory cofinalRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute regularRoute cofinalRoute cofinalPkg
  obtain ⟨_unaryS, _unaryM, unaryQ, unaryF, unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed unaryQ unaryF selectorRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectorUnary unaryR regularRoute
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed regularUnary unaryW cofinalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cofinalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row cofinalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F selectorRead ∧
              Cont selectorRead R regularRead ∧ Cont regularRead W cofinalRead ∧
                PkgSig bundle cofinalRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cofinalRead ⟨hsame_refl cofinalRead, cofinalUnary⟩
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
        ⟨source.right, selectorRoute, regularRoute, cofinalRoute, cofinalPkg,
          provenancePkg⟩
  }
  exact ⟨cert, selectorUnary, regularUnary, cofinalUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
