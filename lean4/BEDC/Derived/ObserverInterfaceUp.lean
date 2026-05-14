import BEDC.Derived.ObserverInterfaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverInterfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverInterfacePacket [AskSetup] [PackageSetup]
    (history filter attention selected omitted licensed stream noSubject transports ledger routes
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory history ∧ UnaryHistory filter ∧ UnaryHistory attention ∧
    UnaryHistory selected ∧ UnaryHistory omitted ∧ UnaryHistory licensed ∧
      UnaryHistory stream ∧ UnaryHistory noSubject ∧ UnaryHistory transports ∧
        UnaryHistory ledger ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
          UnaryHistory name ∧ Cont history filter attention ∧ Cont attention selected ledger ∧
            Cont selected licensed stream ∧ Cont omitted noSubject transports ∧
              Cont routes provenance name ∧ PkgSig bundle name pkg

theorem ObserverInterfacePacket_public_export [AskSetup] [PackageSetup]
    {history filter attention selected omitted licensed stream noSubject transports ledger routes
      provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverInterfacePacket history filter attention selected omitted licensed stream noSubject
        transports ledger routes provenance name bundle pkg →
      Cont stream name consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory selected ∧ UnaryHistory omitted ∧ UnaryHistory licensed ∧
            UnaryHistory stream ∧ UnaryHistory consumer ∧ Cont stream name consumer ∧
              PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro packet streamNameConsumer consumerPkg
  obtain ⟨_historyUnary, _filterUnary, _attentionUnary, selectedUnary, omittedUnary,
    licensedUnary, streamUnary, _noSubjectUnary, _transportsUnary, _ledgerUnary,
    _routesUnary, _provenanceUnary, nameUnary, _historyFilterAttention,
    _attentionSelectedLedger, _selectedLicensedStream, _omittedNoSubjectTransports,
    _routesProvenanceName, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed streamUnary nameUnary streamNameConsumer
  exact
    ⟨selectedUnary, omittedUnary, licensedUnary, streamUnary, consumerUnary,
      streamNameConsumer, namePkg, consumerPkg⟩

end BEDC.Derived.ObserverInterfaceUp
