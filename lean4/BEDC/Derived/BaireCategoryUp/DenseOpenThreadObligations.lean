import BEDC.Derived.BaireCategoryUp.NameCertObligations

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_dense_open_thread_obligations [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead refinementRead threadRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont D O denseRead ->
        Cont denseRead R refinementRead ->
          Cont refinementRead T threadRead ->
            Cont threadRead M limitRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle limitRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row threadRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨
                          hsame row threadRead ∨ hsame row limitRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle limitRead pkg)
                      hsame ∧
                    UnaryHistory denseRead ∧ UnaryHistory refinementRead ∧
                      UnaryHistory threadRead ∧ UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute refinementRoute threadRoute limitRoute packageP limitPkg
  obtain ⟨_baseUnary, metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _provenancePkg⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed denseReadUnary refinementUnary refinementRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementReadUnary threadUnary threadRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed threadReadUnary metricUnary limitRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row threadRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨
              hsame row threadRead ∨ hsame row limitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle limitRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro threadRead ⟨hsame_refl threadRead, threadReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packageP, limitPkg⟩
  }
  exact ⟨cert, denseReadUnary, refinementReadUnary, threadReadUnary, limitReadUnary⟩

end BEDC.Derived.BaireCategoryUp
