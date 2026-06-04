import BEDC.Derived.FastCauchySubsequenceUp.SelectorWindowCoverage

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceSelectedWindowInduction [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead -> Cont modulusRead Q selectorRead ->
        Cont selectorRead F fastRead -> Cont fastRead R regularRead ->
          Cont regularRead W windowRead -> PkgSig bundle windowRead pkg ->
            SemanticNameCert (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨ hsame row W ∨
                  hsame row selectorRead ∨ hsame row windowRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont modulusRead Q selectorRead ∧
                  Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                    Cont regularRead W windowRead ∧ PkgSig bundle windowRead pkg)
              hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory fastRead ∧
                UnaryHistory regularRead ∧ UnaryHistory windowRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier modulusRoute selectorRoute fastRoute regularRoute windowRoute windowPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regularUnary unaryW windowRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨ hsame row W ∨
              hsame row selectorRead ∨ hsame row windowRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulusRead Q selectorRead ∧
              Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                Cont regularRead W windowRead ∧ PkgSig bundle windowRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro windowRead ⟨hsame_refl windowRead, windowUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, selectorRoute, fastRoute, regularRoute, windowRoute, windowPkg⟩
  }
  exact ⟨cert, selectorUnary, fastUnary, regularUnary, windowUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
