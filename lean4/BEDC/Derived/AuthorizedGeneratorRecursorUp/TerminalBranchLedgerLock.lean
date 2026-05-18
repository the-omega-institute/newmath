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

theorem AuthorizedGeneratorRecursorTerminalBranchLedgerLock [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead auditRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont M B branchRead →
        Cont branchRead D outputRead →
          Cont outputRead A auditRead →
            Cont auditRead N terminalRead →
              PkgSig bundle terminalRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                        bundle pkg ∧ hsame row B)
                    (fun row : BHist =>
                      hsame row B ∧ UnaryHistory row ∧ Cont M B branchRead)
                    (fun _row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
                        Cont branchRead D outputRead)
                    hsame ∧
                  UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                    UnaryHistory auditRead ∧ UnaryHistory terminalRead ∧
                      Cont M B branchRead ∧ Cont branchRead D outputRead ∧
                        Cont outputRead A auditRead ∧ Cont auditRead N terminalRead ∧
                          hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier branchCont outputCont auditCont terminalCont terminalPkg
  have carrierPacket :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg :=
    carrier
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, _unaryO, unaryA, sameTransport,
      _unaryC, provenanceUnary, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      sameLedger, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryM unaryB branchCont
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed branchUnary unaryD outputCont
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryA auditCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed auditUnary unaryN terminalCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
              hsame row B)
          (fun row : BHist => hsame row B ∧ UnaryHistory row ∧ Cont M B branchRead)
          (fun _row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
              Cont branchRead D outputRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro B ⟨carrierPacket, hsame_refl B⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport_symm unaryB source.right, branchCont⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, terminalPkg, outputCont⟩
    }
  exact
    ⟨cert, branchUnary, outputUnary, auditUnary, terminalUnary, branchCont, outputCont,
      auditCont, terminalCont, sameLedger, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
