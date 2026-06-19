import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisCarrier_real_handoff_stability [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N completionBasis limitRoute readbackRoute toleranceRoute realRoute
      structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont Q F completionBasis →
        Cont completionBasis L limitRoute →
          Cont limitRoute R readbackRoute →
            Cont readbackRoute D toleranceRoute →
              Cont toleranceRoute E realRoute →
                Cont H C structuralRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle structuralRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row realRoute ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row R ∨
                              hsame row D ∨ hsame row E ∨ hsame row realRoute ∨
                                hsame row structuralRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont Q F completionBasis ∧
                              Cont completionBasis L limitRoute ∧
                                Cont limitRoute R readbackRoute ∧
                                  Cont readbackRoute D toleranceRoute ∧
                                    Cont toleranceRoute E realRoute ∧
                                      Cont H C structuralRead ∧
                                        PkgSig bundle P pkg ∧
                                          PkgSig bundle structuralRead pkg)
                          hsame ∧
                        UnaryHistory readbackRoute ∧ UnaryHistory toleranceRoute ∧
                          UnaryHistory realRoute ∧ UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qf completionLimit limitReadback readTolerance toleranceReal hc pkgP
    pkgStructural
  obtain
    ⟨qUnary, fUnary, lUnary, _wUnary, rUnary, dUnary, eUnary, hUnary, cUnary,
      _pUnary, _nUnary, _sameHN, _carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionBasis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limitRoute :=
    unary_cont_closed completionUnary lUnary completionLimit
  have readbackUnary : UnaryHistory readbackRoute :=
    unary_cont_closed limitUnary rUnary limitReadback
  have toleranceUnary : UnaryHistory toleranceRoute :=
    unary_cont_closed readbackUnary dUnary readTolerance
  have realUnary : UnaryHistory realRoute :=
    unary_cont_closed toleranceUnary eUnary toleranceReal
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary hc
  have sourceReal :
      (fun row : BHist => hsame row realRoute ∧ UnaryHistory row) realRoute := by
    exact ⟨hsame_refl realRoute, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row R ∨
              hsame row D ∨ hsame row E ∨ hsame row realRoute ∨
                hsame row structuralRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F completionBasis ∧
              Cont completionBasis L limitRoute ∧ Cont limitRoute R readbackRoute ∧
                Cont readbackRoute D toleranceRoute ∧ Cont toleranceRoute E realRoute ∧
                  Cont H C structuralRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle structuralRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRoute sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qf, completionLimit, limitReadback, readTolerance, toleranceReal, hc,
          pkgP, pkgStructural⟩
  }
  exact ⟨cert, readbackUnary, toleranceUnary, realUnary, structuralUnary⟩

end BEDC.Derived.FilterLimitBasisUp
