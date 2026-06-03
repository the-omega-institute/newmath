import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cofinal_subsequence_classifier_exactness
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N S' K' R' Q' E' H' C' P' N' classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      BolzanoWeierstrassCarrier S' K' R' Q' E' H' C' P' N' bundle pkg ->
        hsame S S' ->
          hsame K K' ->
            hsame R R' ->
              hsame Q Q' ->
                hsame E E' ->
                  Cont Q Q' classifierRead ->
                    PkgSig bundle classifierRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                              hsame row E ∨ hsame row classifierRead)
                          (fun row : BHist =>
                            hsame row classifierRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle P' pkg ∧ PkgSig bundle classifierRead pkg)
                          hsame ∧
                        UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier carrier' _sameS _sameK _sameR _sameQ _sameE classifierRoute classifierPkg
  obtain ⟨_SUnary, _KUnary, _RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute, carrierPkg⟩ :=
    carrier
  obtain ⟨_SUnary', _KUnary', _RUnary', QUnary', _EUnary', _HUnary', _CUnary',
    _PUnary', _NUnary', _sourceIntervalRoute', _readbackSealRoute',
    _transportReplayRoute', carrierPkg'⟩ := carrier'
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed QUnary QUnary' classifierRoute
  have sourceClassifier :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row) classifierRead := by
    exact ⟨hsame_refl classifierRead, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row classifierRead)
          (fun row : BHist =>
            hsame row classifierRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle P' pkg ∧
              PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceClassifier
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
      exact ⟨source.left, carrierPkg, carrierPkg', classifierPkg⟩
  }
  exact ⟨cert, classifierUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
