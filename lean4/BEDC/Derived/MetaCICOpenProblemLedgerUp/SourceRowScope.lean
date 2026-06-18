import BEDC.Derived.MetaCICOpenProblemLedgerUp

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICOpenProblemLedger_source_row_scope [AskSetup] [PackageSetup]
    {S C N U D E B H R P Q sourceAudit normalCheck blockerRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICOpenProblemLedgerCarrier S C N U D E B H R P Q bundle pkg ->
      Cont S C sourceAudit ->
        Cont N U normalCheck ->
          Cont D E blockerRead ->
            Cont sourceAudit blockerRead ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory U ∧
                  UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory B ∧
                    UnaryHistory sourceAudit ∧ UnaryHistory normalCheck ∧
                      UnaryHistory blockerRead ∧ UnaryHistory ledgerRead ∧
                        Cont S C sourceAudit ∧ Cont N U normalCheck ∧
                          Cont D E blockerRead ∧ Cont sourceAudit blockerRead ledgerRead ∧
                            PkgSig bundle Q pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier sourceRoute normalRoute blockerRoute ledgerRoute ledgerPkg
  obtain ⟨sUnary, cUnary, nUnary, uUnary, dUnary, eUnary, bUnary, _hUnary,
    _rUnary, _pUnary, _qUnary, _subjectConfluenceName, _substitutionDecidableExample,
    _blockerHandoffReplay, _provenancePkg, localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceAudit :=
    unary_cont_closed sUnary cUnary sourceRoute
  have normalUnary : UnaryHistory normalCheck :=
    unary_cont_closed nUnary uUnary normalRoute
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed dUnary eUnary blockerRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sourceUnary blockerUnary ledgerRoute
  exact
    ⟨sUnary, cUnary, nUnary, uUnary, dUnary, eUnary, bUnary, sourceUnary,
      normalUnary, blockerUnary, ledgerUnary, sourceRoute, normalRoute, blockerRoute,
      ledgerRoute, localNamePkg, ledgerPkg⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
