import BEDC.Derived.FilterLimitBasisUp.WindowBasisExhaustion

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisCofinalCauchyEntourageInduction [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N basis limit window readback tolerance terminalSeal
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg ->
      Cont Q F basis ->
        Cont basis L limit ->
          Cont limit W window ->
            Cont window R readback ->
              Cont readback D tolerance ->
                Cont tolerance E terminalSeal ->
                  Cont H C replayRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle terminalSeal pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                                hsame row R ∨ hsame row D ∨ hsame row E ∨
                                  hsame row terminalSeal ∨ hsame row replayRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q F basis ∧ Cont basis L limit ∧
                                Cont limit W window ∧ Cont window R readback ∧
                                  Cont readback D tolerance ∧
                                    Cont tolerance E terminalSeal ∧ Cont H C replayRead ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle terminalSeal pkg)
                            hsame ∧
                          UnaryHistory terminalSeal ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qf basisLimit limitWindow windowRead readTolerance toleranceSeal hc pkgP
    pkgTerminal
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, dUnary, eUnary, hUnary, cUnary,
      _pUnary, _nUnary, _sameHN, _carrierPkg⟩ := carrier
  have basisUnary : UnaryHistory basis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limit :=
    unary_cont_closed basisUnary lUnary basisLimit
  have windowUnary : UnaryHistory window :=
    unary_cont_closed limitUnary wUnary limitWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary rUnary windowRead
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed readbackUnary dUnary readTolerance
  have terminalSealUnary : UnaryHistory terminalSeal :=
    unary_cont_closed toleranceUnary eUnary toleranceSeal
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary hc
  have sourceTerminal :
      (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row) terminalSeal := by
    exact ⟨hsame_refl terminalSeal, terminalSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row E ∨ hsame row terminalSeal ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F basis ∧ Cont basis L limit ∧
              Cont limit W window ∧ Cont window R readback ∧ Cont readback D tolerance ∧
                Cont tolerance E terminalSeal ∧ Cont H C replayRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle terminalSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalSeal sourceTerminal
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, qf, basisLimit, limitWindow, windowRead, readTolerance,
          toleranceSeal, hc, pkgP, pkgTerminal⟩
  }
  exact ⟨cert, terminalSealUnary, replayReadUnary⟩

end BEDC.Derived.FilterLimitBasisUp
