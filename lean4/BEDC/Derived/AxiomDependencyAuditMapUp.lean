import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyAuditMapCarrier [AskSetup] [PackageSetup]
    (K M W A L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory A ∧
    UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont K M L ∧ Cont L A H ∧ Cont H C P ∧
        PkgSig bundle N pkg

theorem AxiomDependencyAuditMap_mode_totality [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        PkgSig bundle modeRead pkg →
          UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory A ∧
            UnaryHistory modeRead ∧ Cont M W modeRead ∧ Cont K M L ∧
              PkgSig bundle N pkg ∧ PkgSig bundle modeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier modeRoute modePkg
  obtain ⟨kUnary, mUnary, wUnary, aUnary, _lUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    namePkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  exact
    ⟨kUnary, mUnary, wUnary, aUnary, modeUnary, modeRoute, claimModeLedger, namePkg,
      modePkg⟩

theorem AxiomDependencyAuditMapCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        PkgSig bundle modeRead pkg →
          UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory A ∧
            UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
              UnaryHistory N ∧ UnaryHistory modeRead ∧ Cont K M L ∧ Cont L A H ∧
                Cont H C P ∧ Cont M W modeRead ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle modeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier modeRoute modePkg
  obtain ⟨kUnary, mUnary, wUnary, aUnary, lUnary, hUnary, cUnary, pUnary,
    nUnary, claimModeLedger, ledgerAxiomTransport, transportConsumerProvenance,
    namePkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  exact
    ⟨kUnary, mUnary, wUnary, aUnary, lUnary, hUnary, cUnary, pUnary, nUnary,
      modeUnary, claimModeLedger, ledgerAxiomTransport, transportConsumerProvenance,
      modeRoute, namePkg, modePkg⟩

theorem AxiomDependencyAuditMapCarrier_nonescape [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        Cont modeRead L ledgerRead →
          Cont ledgerRead N publicRead →
            PkgSig bundle N pkg →
              UnaryHistory publicRead ∧ Cont modeRead L ledgerRead ∧
                Cont ledgerRead N publicRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier modeRoute ledgerRoute publicRoute namePkg
  obtain ⟨_kUnary, mUnary, wUnary, _aUnary, lUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    _carrierPkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modeUnary lUnary ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary nUnary publicRoute
  exact ⟨publicUnary, ledgerRoute, publicRoute, namePkg⟩

theorem AxiomDependencyAuditMapCarrier_obligation_surface [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead ledgerRead publicRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg ->
      Cont M W modeRead ->
        Cont modeRead L ledgerRead ->
          Cont ledgerRead N publicRead ->
            Cont K L auditRead ->
              PkgSig bundle N pkg ->
                PkgSig bundle auditRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row M ∨ hsame row W ∨ hsame row A ∨
                          hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row auditRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K L auditRead ∧
                          PkgSig bundle auditRead pkg)
                      hsame ∧ UnaryHistory modeRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory publicRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: AxiomDependencyAuditMapCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier modeRoute ledgerRoute publicRoute auditRoute _namePkg auditPkg
  obtain ⟨kUnary, mUnary, wUnary, _aUnary, lUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    _carrierPkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modeUnary lUnary ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary nUnary publicRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed kUnary lUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row M ∨ hsame row W ∨ hsame row A ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K L auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, auditRoute, auditPkg⟩
  }
  exact ⟨cert, modeUnary, ledgerUnary, publicUnary, auditUnary⟩

theorem AxiomDependencyAuditMapCarrier_top_window_obligation_route [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead ledgerRead publicRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        Cont modeRead L ledgerRead →
          Cont ledgerRead N publicRead →
            Cont K H dependencyRead →
              PkgSig bundle N pkg →
                PkgSig bundle dependencyRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row M ∨ hsame row W ∨ hsame row A ∨
                          hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row dependencyRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K H dependencyRead ∧
                          PkgSig bundle dependencyRead pkg)
                      hsame ∧ UnaryHistory modeRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory publicRead ∧ UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory SemanticNameCert hsame
  intro carrier modeRoute ledgerRoute publicRoute dependencyRoute _namePkg dependencyPkg
  obtain ⟨kUnary, mUnary, wUnary, _aUnary, lUnary, hUnary, _cUnary, _pUnary,
    nUnary, _claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    _carrierPkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modeUnary lUnary ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary nUnary publicRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed kUnary hUnary dependencyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row M ∨ hsame row W ∨ hsame row A ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K H dependencyRead ∧ PkgSig bundle dependencyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead ⟨hsame_refl dependencyRead, dependencyUnary⟩
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
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, dependencyRoute, dependencyPkg⟩
  }
  exact ⟨cert, modeUnary, ledgerUnary, publicUnary, dependencyUnary⟩

theorem AxiomDependencyAuditMapCarrier_witness_required_axiom_exactness [AskSetup]
    [PackageSetup] {K M W A L H C P N modeRead witnessAxiomRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        Cont W A witnessAxiomRead →
          PkgSig bundle witnessAxiomRead pkg →
            UnaryHistory W ∧ UnaryHistory A ∧ UnaryHistory modeRead ∧
              UnaryHistory witnessAxiomRead ∧ Cont M W modeRead ∧
                Cont W A witnessAxiomRead ∧ PkgSig bundle witnessAxiomRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier modeRoute witnessAxiomRoute witnessAxiomPkg
  obtain ⟨_kUnary, mUnary, wUnary, aUnary, _lUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    _namePkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  have witnessAxiomUnary : UnaryHistory witnessAxiomRead :=
    unary_cont_closed wUnary aUnary witnessAxiomRoute
  exact
    ⟨wUnary, aUnary, modeUnary, witnessAxiomUnary, modeRoute, witnessAxiomRoute,
      witnessAxiomPkg⟩

theorem AxiomDependencyAuditMapCarrier_witness_ledger_totality [AskSetup] [PackageSetup]
    {K M W A L H C P N modeRead witnessAxiomRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyAuditMapCarrier K M W A L H C P N bundle pkg →
      Cont M W modeRead →
        Cont W A witnessAxiomRead →
          Cont modeRead L ledgerRead →
            Cont ledgerRead N publicRead →
              PkgSig bundle witnessAxiomRead pkg →
                PkgSig bundle N pkg →
                  UnaryHistory witnessAxiomRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory publicRead ∧ Cont modeRead L ledgerRead ∧
                      PkgSig bundle witnessAxiomRead pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier modeRoute witnessAxiomRoute ledgerRoute publicRoute witnessAxiomPkg namePkg
  obtain ⟨_kUnary, mUnary, wUnary, aUnary, lUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _claimModeLedger, _ledgerAxiomTransport, _transportConsumerProvenance,
    _carrierPkg⟩ := carrier
  have modeUnary : UnaryHistory modeRead :=
    unary_cont_closed mUnary wUnary modeRoute
  have witnessAxiomUnary : UnaryHistory witnessAxiomRead :=
    unary_cont_closed wUnary aUnary witnessAxiomRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modeUnary lUnary ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary nUnary publicRoute
  exact
    ⟨witnessAxiomUnary, ledgerUnary, publicUnary, ledgerRoute, witnessAxiomPkg, namePkg⟩

end BEDC.Derived.AxiomDependencyAuditMapUp
