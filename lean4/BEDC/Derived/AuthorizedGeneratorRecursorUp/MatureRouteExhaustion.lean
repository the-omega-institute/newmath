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

theorem AuthorizedGeneratorRecursorMatureRouteExhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N rootRead outputRead streamRead realRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E rootRead →
        Cont rootRead O outputRead →
          Cont outputRead C streamRead →
            Cont streamRead P realRead →
              Cont realRead N terminalRead →
                PkgSig bundle terminalRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row I ∨ hsame row E ∨ hsame row O ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row terminalRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont I E rootRead ∧
                          Cont rootRead O outputRead ∧ Cont outputRead C streamRead ∧
                            Cont streamRead P realRead ∧ Cont realRead N terminalRead ∧
                              PkgSig bundle terminalRead pkg)
                      hsame ∧
                    UnaryHistory rootRead ∧ UnaryHistory outputRead ∧
                      UnaryHistory streamRead ∧ UnaryHistory realRead ∧
                        UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier rootRoute outputRoute streamRoute realRoute terminalRoute terminalPkg
  obtain ⟨iUnary, eUnary, _mUnary, _bUnary, _dUnary, oUnary, _aUnary, _hUnary,
    cUnary, pUnary, _gUnary, nUnary, _signatureMotive, _motiveDescent, _auditRoute,
    _transportAuditContinuation, _provenancePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed iUnary eUnary rootRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed rootReadUnary oUnary outputRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed outputReadUnary cUnary streamRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed streamReadUnary pUnary realRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed realReadUnary nUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row E ∨ hsame row O ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I E rootRead ∧ Cont rootRead O outputRead ∧
              Cont outputRead C streamRead ∧ Cont streamRead P realRead ∧
                Cont realRead N terminalRead ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalReadUnary⟩
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
        ⟨source.right, rootRoute, outputRoute, streamRoute, realRoute, terminalRoute,
          terminalPkg⟩
  }
  exact
    ⟨cert, rootReadUnary, outputReadUnary, streamReadUnary, realReadUnary,
      terminalReadUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
