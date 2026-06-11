import BEDC.Derived.MooreOsgoodUp.IteratedLimitHandoff

namespace BEDC.Derived.MooreOsgoodUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MooreOsgoodUniformTailLock [AskSetup] [PackageSetup]
    {W F S U Q R D E H C P N uniformRead scheduleRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreOsgoodCarrier W F S U Q R D E H C P N bundle pkg →
      Cont U Q uniformRead →
        Cont uniformRead R scheduleRead →
          Cont scheduleRead E regularRead →
            PkgSig bundle regularRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scheduleRead ∨ hsame row regularRead)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row Q ∨ hsame row R ∨
                      Cont U Q uniformRead ∨ Cont uniformRead R scheduleRead)
                  (fun row : BHist =>
                    PkgSig bundle regularRead pkg ∧
                      (hsame row regularRead ∨ hsame row scheduleRead))
                  hsame ∧ UnaryHistory uniformRead ∧ UnaryHistory scheduleRead ∧
                UnaryHistory regularRead ∧ Cont U Q uniformRead ∧
                  Cont uniformRead R scheduleRead ∧ Cont scheduleRead E regularRead ∧
                    PkgSig bundle regularRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier uniformRoute scheduleRoute regularRoute regularPkg
  obtain ⟨_wUnary, _fUnary, _sUnary, uUnary, qUnary, rUnary, _dUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed uUnary qUnary uniformRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed uniformUnary rUnary scheduleRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleUnary eUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scheduleRead ∨ hsame row regularRead)
          (fun row : BHist =>
            hsame row U ∨ hsame row Q ∨ hsame row R ∨ Cont U Q uniformRead ∨
              Cont uniformRead R scheduleRead)
          (fun row : BHist =>
            PkgSig bundle regularRead pkg ∧
              (hsame row regularRead ∨ hsame row scheduleRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead (Or.inr (hsame_refl regularRead))
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
        intro row other sameRows sourceRow
        cases sourceRow with
        | inl sameSchedule =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSchedule)
        | inr sameRegular =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameRegular)
    }
    pattern_sound := by
      intro _row _sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr scheduleRoute)))
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow with
      | inl sameSchedule =>
          exact ⟨regularPkg, Or.inr sameSchedule⟩
      | inr sameRegular =>
          exact ⟨regularPkg, Or.inl sameRegular⟩
  }
  exact
    ⟨cert, uniformUnary, scheduleUnary, regularUnary, uniformRoute, scheduleRoute,
      regularRoute, regularPkg⟩

end BEDC.Derived.MooreOsgoodUp
