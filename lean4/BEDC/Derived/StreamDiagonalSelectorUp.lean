import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StreamDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StreamDiagonalSelectorPacket [AskSetup] [PackageSetup]
    (schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory selector ∧ UnaryHistory readback ∧
    UnaryHistory diagonalPacket ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ Cont schedule selector window ∧
        Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
          PkgSig bundle endpoint pkg

theorem StreamDiagonalSelectorPacket_real_handoff [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint window' dyadicLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket
        routes provenance nameCert endpoint bundle pkg ->
      Cont schedule selector window' ->
        Cont window' readback dyadicLedger' ->
          Cont dyadicLedger' diagonalPacket endpoint' ->
            PkgSig bundle endpoint' pkg ->
              StreamDiagonalSelectorPacket schedule selector window' readback dyadicLedger'
                  diagonalPacket routes provenance nameCert endpoint' bundle pkg ∧
                hsame window window' ∧ hsame dyadicLedger dyadicLedger' ∧
                  hsame endpoint endpoint' := by
  intro packet windowRoute ledgerRoute endpointRoute endpointPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, routesUnary,
    provenanceUnary, nameCertUnary, windowOld, ledgerOld, endpointOld, _endpointPkg⟩ := packet
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have dyadicLedgerUnary' : UnaryHistory dyadicLedger' :=
    unary_cont_closed windowUnary' readbackUnary ledgerRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed dyadicLedgerUnary' diagonalUnary endpointRoute
  have sameWindow : hsame window window' :=
    cont_respects_hsame (hsame_refl schedule) (hsame_refl selector) windowOld windowRoute
  have sameDyadicLedger : hsame dyadicLedger dyadicLedger' :=
    cont_respects_hsame sameWindow (hsame_refl readback) ledgerOld ledgerRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameDyadicLedger (hsame_refl diagonalPacket) endpointOld endpointRoute
  exact
    ⟨⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, routesUnary, provenanceUnary,
        nameCertUnary, windowRoute, ledgerRoute, endpointRoute, endpointPkg⟩,
      sameWindow, sameDyadicLedger, sameEndpoint⟩

theorem StreamDiagonalSelectorPacket_selector_determinacy [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint windowPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      Cont schedule selector windowPrime ->
        UnaryHistory windowPrime ∧ hsame window windowPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet scheduleSelectorWindowPrime
  obtain ⟨scheduleUnary, selectorUnary, _readbackUnary, _diagonalUnary, _routesUnary,
    _provenanceUnary, _nameCertUnary, scheduleSelectorWindow, _windowReadbackDyadicLedger,
    _dyadicLedgerDiagonalEndpoint, _endpointPkg⟩ := packet
  have windowPrimeUnary : UnaryHistory windowPrime :=
    unary_cont_closed scheduleUnary selectorUnary scheduleSelectorWindowPrime
  have sameWindow : hsame window windowPrime :=
    cont_respects_hsame (hsame_refl schedule) (hsame_refl selector) scheduleSelectorWindow
      scheduleSelectorWindowPrime
  exact ⟨windowPrimeUnary, sameWindow⟩

theorem StreamDiagonalSelectorPacket_window_transport [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert endpoint
      window' dyadicLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      Cont schedule selector window' ->
        Cont window' readback dyadicLedger' ->
          Cont dyadicLedger' diagonalPacket endpoint' ->
            PkgSig bundle endpoint' pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row window' ∨ hsame row dyadicLedger' ∨ hsame row endpoint')
                  (fun row : BHist =>
                    hsame row schedule ∨ hsame row selector ∨ hsame row window' ∨
                      hsame row readback ∨ hsame row dyadicLedger' ∨
                        hsame row diagonalPacket ∨ hsame row endpoint')
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont schedule selector window' ∧
                      Cont window' readback dyadicLedger' ∧
                        Cont dyadicLedger' diagonalPacket endpoint' ∧
                          PkgSig bundle endpoint' pkg)
                  hsame ∧ hsame window window' ∧ hsame dyadicLedger dyadicLedger' ∧
                    hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet windowRoute ledgerRoute endpointRoute endpointPkg
  obtain ⟨transportedPacket, sameWindow, sameDyadicLedger, sameEndpoint⟩ :=
    StreamDiagonalSelectorPacket_real_handoff packet windowRoute ledgerRoute endpointRoute endpointPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, _routesUnary,
    _provenanceUnary, _nameCertUnary, _windowRoute, _ledgerRoute, _endpointRoute,
    _endpointPkg⟩ := transportedPacket
  have windowUnary : UnaryHistory window' :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have ledgerUnary : UnaryHistory dyadicLedger' :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary diagonalUnary endpointRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row window' ∨ hsame row dyadicLedger' ∨ hsame row endpoint')
        (fun row : BHist =>
          hsame row schedule ∨ hsame row selector ∨ hsame row window' ∨
            hsame row readback ∨ hsame row dyadicLedger' ∨
              hsame row diagonalPacket ∨ hsame row endpoint')
        (fun row : BHist =>
          UnaryHistory row ∧ Cont schedule selector window' ∧
            Cont window' readback dyadicLedger' ∧
              Cont dyadicLedger' diagonalPacket endpoint' ∧ PkgSig bundle endpoint' pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro window' (Or.inl (hsame_refl window'))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        cases source with
        | inl rowWindow =>
            exact Or.inl (hsame_trans (hsame_symm same) rowWindow)
        | inr rest =>
            cases rest with
            | inl rowLedger =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowLedger))
            | inr rowEndpoint =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm same) rowEndpoint))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl rowWindow =>
          exact Or.inr (Or.inr (Or.inl rowWindow))
      | inr rest =>
          cases rest with
          | inl rowLedger =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowLedger))))
          | inr rowEndpoint =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rowEndpoint)))))
    ledger_sound := by
      intro row source
      cases source with
      | inl rowWindow =>
          exact
            ⟨unary_transport windowUnary (hsame_symm rowWindow), windowRoute, ledgerRoute,
              endpointRoute, endpointPkg⟩
      | inr rest =>
          cases rest with
          | inl rowLedger =>
              exact
                ⟨unary_transport ledgerUnary (hsame_symm rowLedger), windowRoute, ledgerRoute,
                  endpointRoute, endpointPkg⟩
          | inr rowEndpoint =>
              exact
                ⟨unary_transport endpointUnary (hsame_symm rowEndpoint), windowRoute, ledgerRoute,
                  endpointRoute, endpointPkg⟩
  }
  exact ⟨cert, sameWindow, sameDyadicLedger, sameEndpoint⟩

theorem StreamDiagonalSelectorPacket_tail_budget_readback [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert endpoint
      tailBudget budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      UnaryHistory tailBudget ->
        Cont window tailBudget budgetRead ->
          PkgSig bundle tailBudget pkg ->
            PkgSig bundle budgetRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
                      hsame row readback ∨ hsame row dyadicLedger ∨
                        hsame row diagonalPacket ∨ hsame row tailBudget ∨
                          hsame row budgetRead ∨ hsame row nameCert)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont schedule selector window ∧
                      Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
                        Cont window tailBudget budgetRead ∧ PkgSig bundle tailBudget pkg ∧
                          PkgSig bundle budgetRead pkg)
                  hsame ∧ UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet tailBudgetUnary budgetRoute tailBudgetPkg budgetReadPkg
  obtain ⟨scheduleUnary, selectorUnary, _readbackUnary, _diagonalUnary, _routesUnary,
    _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute, endpointRoute, _endpointPkg⟩ :=
    packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary tailBudgetUnary budgetRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row schedule ∨ hsame row selector ∨ hsame row window ∨
            hsame row readback ∨ hsame row dyadicLedger ∨
              hsame row diagonalPacket ∨ hsame row tailBudget ∨
                hsame row budgetRead ∨ hsame row nameCert)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont schedule selector window ∧
            Cont window readback dyadicLedger ∧ Cont dyadicLedger diagonalPacket endpoint ∧
              Cont window tailBudget budgetRead ∧ PkgSig bundle tailBudget pkg ∧
                PkgSig bundle budgetRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, windowRoute, ledgerRoute, endpointRoute, budgetRoute, tailBudgetPkg,
          budgetReadPkg⟩
  }
  exact ⟨cert, budgetReadUnary⟩

theorem StreamDiagonalSelectorPacket_window_coverage [AskSetup] [PackageSetup]
    {schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert
      endpoint coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamDiagonalSelectorPacket schedule selector window readback dyadicLedger diagonalPacket routes
        provenance nameCert endpoint bundle pkg ->
      Cont window dyadicLedger coverageRead ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row window ∨ hsame row dyadicLedger ∨ hsame row endpoint ∨
                  hsame row coverageRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont schedule selector window ∧
                  Cont window readback dyadicLedger ∧
                    Cont dyadicLedger diagonalPacket endpoint ∧
                      Cont window dyadicLedger coverageRead ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory coverageRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet coverageRoute endpointPkg
  obtain ⟨scheduleUnary, selectorUnary, readbackUnary, diagonalUnary, _routesUnary,
    _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute, endpointRoute,
    _endpointPkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary selectorUnary windowRoute
  have ledgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary diagonalUnary endpointRoute
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed windowUnary ledgerUnary coverageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row dyadicLedger ∨ hsame row endpoint ∨
              hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont schedule selector window ∧
              Cont window readback dyadicLedger ∧
                Cont dyadicLedger diagonalPacket endpoint ∧
                  Cont window dyadicLedger coverageRead ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverageRead ⟨hsame_refl coverageRead, coverageUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, ledgerRoute, endpointRoute, coverageRoute, endpointPkg⟩
  }
  exact ⟨cert, coverageUnary⟩

end BEDC.Derived.StreamDiagonalSelectorUp
