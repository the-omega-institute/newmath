import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PaperLeanDriftWitnessCarrier [AskSetup] [PackageSetup]
    (M A L I R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont M A L ∧ Cont L I R ∧ Cont R H C ∧
        PkgSig bundle N pkg

theorem PaperLeanDriftWitness_audit_consumer_kernel_scope [AskSetup] [PackageSetup]
    {M A L I R H C P N terminal : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R C terminal →
        PkgSig bundle terminal pkg →
          UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
            UnaryHistory R ∧ UnaryHistory terminal ∧ Cont R C terminal ∧
              PkgSig bundle N pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier terminalRoute terminalPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, _hUnary, cUnary, _pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed rUnary cUnary terminalRoute
  exact
    ⟨mUnary, aUnary, lUnary, iUnary, rUnary, terminalUnary, terminalRoute, namePkg,
      terminalPkg⟩

theorem PaperLeanDriftWitness_resolution_ledger_kernel_scope [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H verdictRead →
        PkgSig bundle verdictRead pkg →
          UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
            UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory verdictRead ∧
              Cont M A L ∧ Cont L I R ∧ Cont R H verdictRead ∧
                PkgSig bundle N pkg ∧ PkgSig bundle verdictRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier verdictRoute verdictPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, _cUnary, _pUnary, _nUnary,
    markerNameLedger, ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  exact
    ⟨mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, verdictUnary, markerNameLedger,
      ledgerInventoryVerdict, verdictRoute, namePkg, verdictPkg⟩

theorem PaperLeanDriftWitness_verdict_determinism [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H verdictRead →
        Cont verdictRead C auditRead →
          PkgSig bundle auditRead pkg →
            UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
              UnaryHistory R ∧ UnaryHistory verdictRead ∧ UnaryHistory auditRead ∧
                Cont L I R ∧ Cont R H verdictRead ∧ Cont verdictRead C auditRead ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier verdictRoute auditRoute auditPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, cUnary, _pUnary, _nUnary,
    _markerNameLedger, ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed verdictUnary cUnary auditRoute
  exact
    ⟨mUnary, aUnary, lUnary, iUnary, rUnary, verdictUnary, auditUnary,
      ledgerInventoryVerdict, verdictRoute, auditRoute, namePkg, auditPkg⟩

theorem PaperLeanDriftWitness_namecert_obligations [AskSetup] [PackageSetup]
    {M A L I R H C P N auditRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont R H auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row auditRead)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
              UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory auditRead ∧
                Cont M A L ∧ Cont L I R ∧ Cont R H auditRead ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier auditRoute auditPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, _cUnary, _pUnary, _nUnary,
    markerNameLedger, ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed rUnary hUnary auditRoute
  have sourceAtAudit : hsame auditRead auditRead ∧ UnaryHistory auditRead :=
    ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row auditRead)
          (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAtAudit
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact
    ⟨cert, mUnary, aUnary, lUnary, iUnary, rUnary, hUnary, auditUnary,
      markerNameLedger, ledgerInventoryVerdict, auditRoute, namePkg, auditPkg⟩

theorem PaperLeanDriftWitness_resolution_exactness [AskSetup] [PackageSetup]
    {M A L I R H C P N exactRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont L I exactRead →
        Cont exactRead R replayRead →
          PkgSig bundle replayRead pkg →
            UnaryHistory M ∧ UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory I ∧
              UnaryHistory exactRead ∧ UnaryHistory replayRead ∧ Cont L I exactRead ∧
                Cont exactRead R replayRead ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier exactRoute replayRoute replayPkg
  obtain ⟨mUnary, aUnary, lUnary, iUnary, rUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed lUnary iUnary exactRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed exactUnary rUnary replayRoute
  exact
    ⟨mUnary, aUnary, lUnary, iUnary, exactUnary, replayUnary, exactRoute, replayRoute,
      namePkg, replayPkg⟩

theorem PaperLeanDriftWitness_public_resolution_export [AskSetup] [PackageSetup]
    {M A L I R H C P N verdictRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg →
      Cont R H verdictRead →
        Cont verdictRead C auditRead →
          Cont auditRead P publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory verdictRead ∧ UnaryHistory auditRead ∧
                UnaryHistory publicRead ∧ hsame verdictRead (append R H) ∧
                  hsame auditRead (append verdictRead C) ∧
                    hsame publicRead (append auditRead P) ∧ Cont R H verdictRead ∧
                      Cont verdictRead C auditRead ∧ Cont auditRead P publicRead ∧
                        PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier verdictRoute auditRoute publicRoute publicPkg
  obtain ⟨_mUnary, _aUnary, _lUnary, _iUnary, rUnary, hUnary, cUnary, pUnary, _nUnary,
    _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer, namePkg⟩ :=
    carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed rUnary hUnary verdictRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed verdictUnary cUnary auditRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary pUnary publicRoute
  exact
    ⟨verdictUnary, auditUnary, publicUnary, verdictRoute, auditRoute, publicRoute,
      verdictRoute, auditRoute, publicRoute, namePkg, publicPkg⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
