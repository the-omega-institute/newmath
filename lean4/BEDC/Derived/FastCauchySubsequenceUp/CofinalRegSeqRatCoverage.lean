import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalRegSeqRatCoverage [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N cofinalRead regRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont Q F cofinalRead ->
        Cont cofinalRead R regRead ->
          PkgSig bundle regRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row regRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
                    hsame row W ∨ hsame row cofinalRead ∨ hsame row regRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle regRead pkg ∧
                    Cont Q F cofinalRead ∧ Cont cofinalRead R regRead)
                hsame ∧ UnaryHistory cofinalRead ∧ UnaryHistory regRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier cofinalRoute regRoute regPkg
  obtain ⟨_unaryS, _unaryM, unaryQ, unaryF, unaryR, _unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed unaryQ unaryF cofinalRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed cofinalUnary unaryR regRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row cofinalRead ∨ hsame row regRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle regRead pkg ∧ Cont Q F cofinalRead ∧
              Cont cofinalRead R regRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regRead ⟨hsame_refl regRead, regUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regPkg, cofinalRoute, regRoute⟩
  }
  exact ⟨cert, cofinalUnary, regUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
