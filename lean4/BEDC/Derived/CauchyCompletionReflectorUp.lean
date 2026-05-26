import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionReflectorPacket [AskSetup] [PackageSetup]
    (source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory source ∧ UnaryHistory completionObject ∧ UnaryHistory unit ∧
    UnaryHistory counit ∧ UnaryHistory idempotent ∧ UnaryHistory extension ∧
      UnaryHistory reflection ∧ UnaryHistory transport ∧ UnaryHistory componentTransport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          UnaryHistory exported ∧ Cont source unit completionObject ∧
            Cont completionObject counit transport ∧ Cont idempotent extension reflection ∧
              Cont componentTransport replay provenance ∧ Cont provenance localName exported ∧
                PkgSig bundle exported pkg

theorem CauchyCompletionReflectorPacket_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent
        extension reflection transport componentTransport replay provenance localName exported
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyCompletionReflectorPacket source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName exported
              bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          CauchyCompletionReflectorPacket source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName exported
              bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          CauchyCompletionReflectorPacket source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName exported
              bundle pkg ∧
            hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨packet, hsame_refl localName⟩
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
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyCompletionReflectorPacket_real_transport_nonescape
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent
        extension reflection transport componentTransport replay provenance localName exported
        bundle pkg →
      Cont transport exported realConsumer →
        PkgSig bundle realConsumer pkg →
          UnaryHistory realConsumer ∧ Cont source unit completionObject ∧
            Cont completionObject counit transport ∧ Cont transport exported realConsumer ∧
              PkgSig bundle exported pkg ∧ PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet realConsumerRoute realConsumerPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, _unitUnary, _counitUnary, _idempotentUnary,
      _extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, exportedUnary, sourceRoute,
      completionRoute, _idempotentRoute, _componentRoute, _provenanceRoute, exportedPkg⟩
  exact ⟨unary_cont_closed transportUnary exportedUnary realConsumerRoute, sourceRoute,
    completionRoute, realConsumerRoute, exportedPkg, realConsumerPkg⟩

theorem CauchyCompletionReflectorPacket_reflection_scope
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported reflectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent
        extension reflection transport componentTransport replay provenance localName exported
        bundle pkg →
      Cont extension reflection reflectionRead →
        PkgSig bundle reflectionRead pkg →
          UnaryHistory reflectionRead ∧ Cont source unit completionObject ∧
            Cont completionObject counit transport ∧ Cont idempotent extension reflection ∧
              Cont extension reflection reflectionRead ∧ PkgSig bundle exported pkg ∧
                PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet reflectionReadRoute reflectionReadPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, _unitUnary, _counitUnary, _idempotentUnary,
      extensionUnary, reflectionUnary, _transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, sourceRoute,
      completionRoute, idempotentRoute, _componentRoute, _provenanceRoute, exportedPkg⟩
  exact ⟨unary_cont_closed extensionUnary reflectionUnary reflectionReadRoute, sourceRoute,
    completionRoute, idempotentRoute, reflectionReadRoute, exportedPkg, reflectionReadPkg⟩

end BEDC.Derived.CauchyCompletionReflectorUp
