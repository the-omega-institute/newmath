import BEDC.Derived.BaireCategoryUp.NameCertObligations

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_dense_open_schedule_scope [AskSetup] [PackageSetup]
    {B M D O R T H C P N scheduleRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg →
      Cont D O scheduleRead →
        Cont scheduleRead R replayRead →
          PkgSig bundle replayRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scheduleRead ∨ hsame row replayRead)
                (fun row : BHist =>
                  hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨
                    hsame row scheduleRead ∨ hsame row replayRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ (hsame row scheduleRead ∨ hsame row replayRead))
                hsame ∧
              UnaryHistory scheduleRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleRoute replayRoute _replayPkg
  obtain ⟨_baseUnary, _metricUnary, denseUnary, openUnary, refinementUnary, _threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed denseUnary openUnary scheduleRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed scheduleUnary refinementUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scheduleRead ∨ hsame row replayRead)
          (fun row : BHist =>
            hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨
              hsame row scheduleRead ∨ hsame row replayRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row scheduleRead ∨ hsame row replayRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scheduleRead (Or.inl (hsame_refl scheduleRead))
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
        | inl sameSchedule =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSchedule)
        | inr sameReplay =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameSchedule =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSchedule))))
      | inr sameReplay =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameReplay))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact ⟨cert, scheduleUnary, replayUnary⟩

end BEDC.Derived.BaireCategoryUp
