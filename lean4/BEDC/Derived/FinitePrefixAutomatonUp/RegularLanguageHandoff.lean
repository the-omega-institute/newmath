import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixAutomaton_regular_language_handoff [AskSetup] [PackageSetup]
    {q q0 a t w r e h c p n handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FinitePrefixAutomatonCarrier q q0 a t w r e h c p n bundle pkg ->
      Cont r e handoff ->
        PkgSig bundle handoff pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row w ∨ hsame row r ∨ hsame row e ∨ hsame row handoff)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle handoff pkg ∧ PkgSig bundle n pkg)
              hsame ∧
            UnaryHistory handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier rEHandoff handoffPkg
  obtain ⟨_qUnary, _q0Unary, _aUnary, _tUnary, _wUnary, rUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _sameQT, _sameQ0W, _sameAR, _sameHE, _sameCT,
    _samePW, _sameNR, _pkgP, pkgN⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed rUnary eUnary rEHandoff
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row w ∨ hsame row r ∨ hsame row e ∨ hsame row handoff)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle handoff pkg ∧ PkgSig bundle n pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro handoff
          (And.intro (hsame_refl handoff) handoffUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact And.intro source.right (And.intro handoffPkg pkgN)
    }
  exact And.intro cert handoffUnary

end BEDC.Derived.FinitePrefixAutomatonUp
