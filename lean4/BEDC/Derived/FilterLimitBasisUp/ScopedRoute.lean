import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisScopedRoute [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N completionBasis limitRoute readbackRoute
      toleranceRoute realRoute structuralRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont Q F completionBasis →
        Cont completionBasis L limitRoute →
          Cont limitRoute R readbackRoute →
            Cont readbackRoute D toleranceRoute →
              Cont toleranceRoute E realRoute →
                Cont H C structuralRead →
                  Cont realRoute N scopedRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle scopedRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row F ∨ hsame row L ∨
                                hsame row W ∨ hsame row R ∨ hsame row D ∨
                                  hsame row E ∨ hsame row H ∨ hsame row C ∨
                                    hsame row P ∨ hsame row N ∨
                                      hsame row completionBasis ∨
                                        hsame row limitRoute ∨
                                          hsame row readbackRoute ∨
                                            hsame row toleranceRoute ∨
                                              hsame row realRoute ∨
                                                hsame row structuralRead ∨
                                                  hsame row scopedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q F completionBasis ∧
                                Cont completionBasis L limitRoute ∧
                                  Cont limitRoute R readbackRoute ∧
                                    Cont readbackRoute D toleranceRoute ∧
                                      Cont toleranceRoute E realRoute ∧
                                        Cont H C structuralRead ∧
                                          Cont realRoute N scopedRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle scopedRead pkg)
                            hsame ∧
                          UnaryHistory completionBasis ∧ UnaryHistory limitRoute ∧
                            UnaryHistory readbackRoute ∧
                              UnaryHistory toleranceRoute ∧ UnaryHistory realRoute ∧
                                UnaryHistory structuralRead ∧
                                  UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier qf completionLimit limitReadback readbackTolerance toleranceReal
    structuralRoute scopedRoute pkgP pkgScoped
  obtain
    ⟨qUnary, fUnary, lUnary, _wUnary, rUnary, dUnary, eUnary, hUnary, cUnary,
      _pUnary, nUnary, _sameHN, _carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionBasis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limitRoute :=
    unary_cont_closed completionUnary lUnary completionLimit
  have readbackUnary : UnaryHistory readbackRoute :=
    unary_cont_closed limitUnary rUnary limitReadback
  have toleranceUnary : UnaryHistory toleranceRoute :=
    unary_cont_closed readbackUnary dUnary readbackTolerance
  have realUnary : UnaryHistory realRoute :=
    unary_cont_closed toleranceUnary eUnary toleranceReal
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed realUnary nUnary scopedRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row completionBasis ∨ hsame row limitRoute ∨
                    hsame row readbackRoute ∨ hsame row toleranceRoute ∨
                      hsame row realRoute ∨ hsame row structuralRead ∨
                        hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F completionBasis ∧
              Cont completionBasis L limitRoute ∧
                Cont limitRoute R readbackRoute ∧
                  Cont readbackRoute D toleranceRoute ∧
                    Cont toleranceRoute E realRoute ∧
                      Cont H C structuralRead ∧ Cont realRoute N scopedRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceScoped
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qf, completionLimit, limitReadback, readbackTolerance,
          toleranceReal, structuralRoute, scopedRoute, pkgP, pkgScoped⟩
  }
  exact
    ⟨cert, completionUnary, limitUnary, readbackUnary, toleranceUnary, realUnary,
      structuralUnary, scopedUnary⟩

end BEDC.Derived.FilterLimitBasisUp
