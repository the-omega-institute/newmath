import BEDC.Derived.BaireOneFunctionUp

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireOneFunctionCarrier_oscillation_locality [AskSetup] [PackageSetup]
    {X F S Q R L H C P N oscillationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont X F S ->
        Cont S Q R ->
          Cont R L oscillationRead ->
            PkgSig bundle oscillationRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row oscillationRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
                      Cont R L oscillationRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle oscillationRead pkg)
                  hsame ∧
                UnaryHistory oscillationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceApproxSchedule scheduleReadbackReal realOscillationRead
    oscillationPkg
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, realUnary, handoffUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierSourceApproxSchedule,
    _carrierScheduleReadbackReal, _carrierRealHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have oscillationUnary : UnaryHistory oscillationRead :=
    unary_cont_closed realUnary handoffUnary realOscillationRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row oscillationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧ Cont R L oscillationRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle oscillationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro oscillationRead
        ⟨hsame_refl oscillationRead, oscillationUnary⟩
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
      exact
        ⟨source.right, sourceApproxSchedule, scheduleReadbackReal, realOscillationRead,
          provenancePkg, oscillationPkg⟩
  }
  exact ⟨cert, oscillationUnary⟩

end BEDC.Derived.BaireOneFunctionUp
