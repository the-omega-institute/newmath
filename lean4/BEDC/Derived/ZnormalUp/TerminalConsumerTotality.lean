import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalConsumerTotality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal terminalRead →
        Cont normal continuation normalRead →
          Cont normalRead name exportRow →
            PkgSig bundle exportRow pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row exportRow ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row normalRead ∨ hsame row exportRow)
                    (fun row : BHist => PkgSig bundle exportRow pkg ∧ hsame row exportRow)
                    hsame ∧
                UnaryHistory terminalRead ∧ UnaryHistory normalRead ∧ UnaryHistory exportRow ∧
                  Cont terminal normal terminalRead ∧ Cont normal continuation normalRead ∧
                    Cont normalRead name exportRow ∧ PkgSig bundle exportRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet terminalNormalRead normalContinuationRead readNameExport exportPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed normalReadUnary nameUnary readNameExport
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRow ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminalRead ∨ hsame row normalRead ∨ hsame row exportRow)
        (fun row : BHist => PkgSig bundle exportRow pkg ∧ hsame row exportRow)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRow (And.intro (hsame_refl exportRow) exportUnary)
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
        intro row row' sameRows sourceRow
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact And.intro exportPkg sourceRow.left
  }
  exact
    And.intro cert
      (And.intro terminalReadUnary
        (And.intro normalReadUnary
          (And.intro exportUnary
            (And.intro terminalNormalRead
              (And.intro normalContinuationRead
                (And.intro readNameExport exportPkg))))))

end BEDC.Derived.ZnormalUp
