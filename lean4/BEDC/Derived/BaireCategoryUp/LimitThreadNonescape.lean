import BEDC.Derived.BaireCategoryUp.NameCertObligations

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_limit_thread_nonescape [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead threadRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont D O denseRead ->
        Cont R T threadRead ->
          Cont threadRead M limitRead ->
            PkgSig bundle limitRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row threadRead ∨ hsame row limitRead)
                  (fun row : BHist => UnaryHistory row)
                  (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
                  hsame ∧
                UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute threadRoute limitRoute _limitPkg
  obtain ⟨_prefixUnary, metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have _denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed threadReadUnary metricUnary limitRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row threadRead ∨ hsame row limitRead)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro threadRead (Or.inl (hsame_refl threadRead))
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
        | inl sameThread =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameThread)
        | inr sameLimit =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameLimit)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameThread =>
          exact unary_transport threadReadUnary (hsame_symm sameThread)
      | inr sameLimit =>
          exact unary_transport limitReadUnary (hsame_symm sameLimit)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }
  exact ⟨cert, limitReadUnary⟩

end BEDC.Derived.BaireCategoryUp
