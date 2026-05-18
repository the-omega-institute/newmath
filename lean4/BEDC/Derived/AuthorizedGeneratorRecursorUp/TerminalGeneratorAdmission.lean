import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalGeneratorAdmission [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D outputRead ->
        Cont outputRead A auditRead ->
          Cont auditRead N terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                      hsame row terminalRead)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨
                      hsame row D ∨ hsame row O ∨ hsame row A ∨
                        hsame row terminalRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
                      hsame row terminalRead)
                  hsame ∧
                UnaryHistory terminalRead ∧ Cont B D outputRead ∧
                  Cont outputRead A auditRead ∧ Cont auditRead N terminalRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier outputCont auditCont terminalCont terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, _unaryO, unaryA, _unaryH, _unaryC,
      _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA, _sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryB unaryD outputCont
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryA auditCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed auditUnary unaryN terminalCont
  have carrierCopy :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, _unaryO, unaryA, _unaryH, _unaryC,
        _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA, _sameTransport,
        provenancePkg⟩
  have sourceTerminal :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row terminalRead) terminalRead := by
    exact ⟨carrierCopy, hsame_refl terminalRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
            hsame row terminalRead)
        (fun row : BHist =>
          hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨ hsame row D ∨
            hsame row O ∨ hsame row A ∨ hsame row terminalRead)
        (fun row : BHist =>
          PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧ hsame row terminalRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceTerminal
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, terminalPkg, source.right⟩
  }
  exact ⟨cert, terminalUnary, outputCont, auditCont, terminalCont, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
