import BEDC.Derived.FastCauchySubsequenceUp.CofinalWindowObligation

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalWindowCertificate [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead cofinalWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead W cofinalWindow ->
            PkgSig bundle cofinalWindow pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row cofinalWindow ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row W ∨
                      hsame row modulusRead ∨ hsame row selectorRead ∨
                        hsame row cofinalWindow)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S M modulusRead ∧
                      Cont modulusRead Q selectorRead ∧
                        Cont selectorRead W cofinalWindow ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle cofinalWindow pkg)
                  hsame := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusRoute selectorRoute cofinalRoute cofinalPkg
  obtain ⟨unaryS, unaryM, unaryQ, _unaryF, _unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have cofinalUnary : UnaryHistory cofinalWindow :=
    unary_cont_closed selectorUnary unaryW cofinalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro cofinalWindow ⟨hsame_refl cofinalWindow, cofinalUnary⟩
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
      exact
        ⟨source.right, modulusRoute, selectorRoute, cofinalRoute, provenancePkg,
          cofinalPkg⟩
  }

end BEDC.Derived.FastCauchySubsequenceUp
