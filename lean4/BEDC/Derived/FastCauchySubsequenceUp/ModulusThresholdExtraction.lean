import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceModulusThresholdExtraction [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead M thresholdRead ->
            PkgSig bundle thresholdRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row M ∨ hsame row Q ∨
                      hsame row modulusRead ∨ hsame row selectorRead ∨
                        hsame row thresholdRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S M modulusRead ∧
                      Cont modulusRead Q selectorRead ∧
                        Cont selectorRead M thresholdRead ∧
                          PkgSig bundle thresholdRead pkg)
                  hsame ∧ UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                UnaryHistory thresholdRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusRoute selectorRoute thresholdRoute thresholdPkg
  obtain ⟨unaryS, unaryM, unaryQ, _unaryF, _unaryR, _unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed selectorUnary unaryM thresholdRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row modulusRead ∨
              hsame row selectorRead ∨ hsame row thresholdRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M modulusRead ∧
              Cont modulusRead Q selectorRead ∧ Cont selectorRead M thresholdRead ∧
                PkgSig bundle thresholdRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro thresholdRead ⟨hsame_refl thresholdRead, thresholdUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusRoute, selectorRoute, thresholdRoute, thresholdPkg⟩
  }
  exact ⟨cert, modulusUnary, selectorUnary, thresholdUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
