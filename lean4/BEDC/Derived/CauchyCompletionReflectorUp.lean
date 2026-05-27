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

theorem CauchyCompletionReflectorPacket_unit_counit_route [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported returnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont transport provenance returnRead →
        PkgSig bundle returnRead pkg →
          UnaryHistory source ∧ UnaryHistory unit ∧ UnaryHistory completionObject ∧
            UnaryHistory counit ∧ UnaryHistory transport ∧ UnaryHistory returnRead ∧
              Cont source unit completionObject ∧ Cont completionObject counit transport ∧
                Cont transport provenance returnRead ∧ PkgSig bundle exported pkg ∧
                  PkgSig bundle returnRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro packet returnCont returnPkg
  rcases packet with
    ⟨sourceUnary, completionUnary, unitUnary, counitUnary, _idempotentUnary,
      _extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, provenanceUnary, _localNameUnary, _exportedUnary, sourceUnitCont,
      completionCounitCont, _idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed transportUnary provenanceUnary returnCont
  exact ⟨sourceUnary, unitUnary, completionUnary, counitUnary, transportUnary, returnUnary,
    sourceUnitCont, completionCounitCont, returnCont, exportedPkg, returnPkg⟩

theorem CauchyCompletionReflectorPacket_unit_counit_obligation [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported returnRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg ->
      Cont transport exported returnRead ->
        PkgSig bundle returnRead pkg ->
          UnaryHistory source ∧ UnaryHistory unit ∧ UnaryHistory completionObject ∧
            UnaryHistory counit ∧ UnaryHistory transport ∧ UnaryHistory exported ∧
              UnaryHistory returnRead ∧ Cont source unit completionObject ∧
                Cont completionObject counit transport ∧ Cont transport exported returnRead ∧
                  PkgSig bundle exported pkg ∧ PkgSig bundle returnRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro packet returnCont returnPkg
  rcases packet with
    ⟨sourceUnary, completionUnary, unitUnary, counitUnary, _idempotentUnary,
      _extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, exportedUnary, sourceUnitCont,
      completionCounitCont, _idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed transportUnary exportedUnary returnCont
  exact ⟨sourceUnary, unitUnary, completionUnary, counitUnary, transportUnary,
    exportedUnary, returnUnary, sourceUnitCont, completionCounitCont, returnCont,
    exportedPkg, returnPkg⟩

theorem CauchyCompletionReflectorPacket_idempotent_extension_obligation
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported reflectedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont reflection transport reflectedRoute →
        PkgSig bundle reflectedRoute pkg →
          UnaryHistory idempotent ∧ UnaryHistory extension ∧ UnaryHistory reflection ∧
            UnaryHistory transport ∧ UnaryHistory reflectedRoute ∧
              Cont idempotent extension reflection ∧
                Cont reflection transport reflectedRoute ∧ PkgSig bundle exported pkg ∧
                  PkgSig bundle reflectedRoute pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro packet reflectedCont reflectedPkg
  rcases packet with
    ⟨_sourceUnary, _completionUnary, _unitUnary, _counitUnary, idempotentUnary,
      extensionUnary, reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, _sourceUnitCont,
      _completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have reflectedUnary : UnaryHistory reflectedRoute :=
    unary_cont_closed reflectionUnary transportUnary reflectedCont
  exact ⟨idempotentUnary, extensionUnary, reflectionUnary, transportUnary, reflectedUnary,
    idempotentExtensionCont, reflectedCont, exportedPkg, reflectedPkg⟩

theorem CauchyCompletionReflectorPacket_naturality_square [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont unit extension leftRead →
        Cont transport counit rightRead →
          PkgSig bundle leftRead pkg →
            PkgSig bundle rightRead pkg →
              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                Cont unit extension leftRead ∧ Cont transport counit rightRead ∧
                  Cont source unit completionObject ∧ Cont completionObject counit transport ∧
                    Cont idempotent extension reflection ∧ PkgSig bundle exported pkg ∧
                      PkgSig bundle leftRead pkg ∧ PkgSig bundle rightRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet leftRoute rightRoute leftPkg rightPkg
  rcases packet with
    ⟨_sourceUnary, _completionUnary, unitUnary, counitUnary, _idempotentUnary,
      extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, sourceUnitCont,
      completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed unitUnary extensionUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed transportUnary counitUnary rightRoute
  exact ⟨leftUnary, rightUnary, leftRoute, rightRoute, sourceUnitCont, completionCounitCont,
    idempotentExtensionCont, exportedPkg, leftPkg, rightPkg⟩

theorem CauchyCompletionReflectorPacket_extension_reflection_scope [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported extensionRead reflectionRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont unit extension extensionRead →
        Cont extension reflection reflectionRead →
          PkgSig bundle reflectionRead pkg →
            UnaryHistory extensionRead ∧ UnaryHistory reflectionRead ∧
              Cont source unit completionObject ∧ Cont completionObject counit transport ∧
                Cont idempotent extension reflection ∧ Cont unit extension extensionRead ∧
                  Cont extension reflection reflectionRead ∧ PkgSig bundle exported pkg ∧
                    PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet extensionRoute reflectionRoute reflectionPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, unitUnary, _counitUnary, _idempotentUnary,
      extensionUnary, reflectionUnary, _transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, sourceUnitCont,
      completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed unitUnary extensionUnary extensionRoute
  have reflectionReadUnary : UnaryHistory reflectionRead :=
    unary_cont_closed extensionUnary reflectionUnary reflectionRoute
  exact ⟨extensionReadUnary, reflectionReadUnary, sourceUnitCont, completionCounitCont,
    idempotentExtensionCont, extensionRoute, reflectionRoute, exportedPkg, reflectionPkg⟩

theorem CauchyCompletionReflectorPacket_public_obligation_package [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported publicRead reflectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont transport exported publicRead →
        Cont reflection transport reflectedRead →
          PkgSig bundle publicRead pkg →
            PkgSig bundle reflectedRead pkg →
              UnaryHistory unit ∧ UnaryHistory counit ∧ UnaryHistory idempotent ∧
                UnaryHistory publicRead ∧ UnaryHistory reflectedRead ∧
                  Cont source unit completionObject ∧
                    Cont completionObject counit transport ∧
                      Cont idempotent extension reflection ∧
                        Cont transport exported publicRead ∧
                          Cont reflection transport reflectedRead ∧ PkgSig bundle exported pkg ∧
                            PkgSig bundle publicRead pkg ∧
                              PkgSig bundle reflectedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet publicRoute reflectedRoute publicPkg reflectedPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, unitUnary, counitUnary, idempotentUnary,
      _extensionUnary, reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, exportedUnary, sourceUnitCont,
      completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed transportUnary exportedUnary publicRoute
  have reflectedUnary : UnaryHistory reflectedRead :=
    unary_cont_closed reflectionUnary transportUnary reflectedRoute
  exact ⟨unitUnary, counitUnary, idempotentUnary, publicUnary, reflectedUnary,
    sourceUnitCont, completionCounitCont, idempotentExtensionCont, publicRoute,
    reflectedRoute, exportedPkg, publicPkg, reflectedPkg⟩

theorem CauchyCompletionReflectorPacket_obligation_closure_package
    [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported publicRead reflectedRead leftRead
      rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont transport exported publicRead →
        Cont reflection transport reflectedRead →
          Cont unit extension leftRead →
            Cont transport counit rightRead →
              PkgSig bundle publicRead pkg →
                PkgSig bundle reflectedRead pkg →
                  PkgSig bundle leftRead pkg →
                    PkgSig bundle rightRead pkg →
                      UnaryHistory publicRead ∧ UnaryHistory reflectedRead ∧
                        UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                          Cont source unit completionObject ∧
                            Cont completionObject counit transport ∧
                              Cont idempotent extension reflection ∧
                                Cont transport exported publicRead ∧
                                  Cont reflection transport reflectedRead ∧
                                    Cont unit extension leftRead ∧
                                      Cont transport counit rightRead ∧
                                        PkgSig bundle exported pkg ∧
                                          PkgSig bundle publicRead pkg ∧
                                            PkgSig bundle reflectedRead pkg ∧
                                              PkgSig bundle leftRead pkg ∧
                                                PkgSig bundle rightRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet publicRoute reflectedRoute leftRoute rightRoute publicPkg reflectedPkg leftPkg
    rightPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, unitUnary, counitUnary, idempotentUnary,
      extensionUnary, reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, exportedUnary, sourceUnitCont,
      completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed transportUnary exportedUnary publicRoute
  have reflectedUnary : UnaryHistory reflectedRead :=
    unary_cont_closed reflectionUnary transportUnary reflectedRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed unitUnary extensionUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed transportUnary counitUnary rightRoute
  exact
    ⟨publicUnary, reflectedUnary, leftUnary, rightUnary, sourceUnitCont, completionCounitCont,
      idempotentExtensionCont, publicRoute, reflectedRoute, leftRoute, rightRoute,
      exportedPkg, publicPkg, reflectedPkg, leftPkg, rightPkg⟩

theorem CauchyCompletionReflectorPacket_idempotent_nonescape [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported repeatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont idempotent transport repeatedRead →
        PkgSig bundle repeatedRead pkg →
          UnaryHistory idempotent ∧ UnaryHistory transport ∧ UnaryHistory repeatedRead ∧
            Cont idempotent extension reflection ∧ Cont idempotent transport repeatedRead ∧
              PkgSig bundle exported pkg ∧ PkgSig bundle repeatedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet repeatedRoute repeatedPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, _unitUnary, _counitUnary, idempotentUnary,
      _extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, _sourceUnitCont,
      _completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have repeatedUnary : UnaryHistory repeatedRead :=
    unary_cont_closed idempotentUnary transportUnary repeatedRoute
  exact ⟨idempotentUnary, transportUnary, repeatedUnary, idempotentExtensionCont,
    repeatedRoute, exportedPkg, repeatedPkg⟩

theorem CauchyCompletionReflectorPacket_idempotent_scope [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported extensionRead reflectionRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont unit extension extensionRead →
        Cont extension reflection reflectionRead →
          PkgSig bundle reflectionRead pkg →
            UnaryHistory idempotent ∧ UnaryHistory extension ∧ UnaryHistory reflection ∧
              UnaryHistory extensionRead ∧ UnaryHistory reflectionRead ∧
                Cont source unit completionObject ∧ Cont completionObject counit transport ∧
                  Cont idempotent extension reflection ∧ Cont unit extension extensionRead ∧
                    Cont extension reflection reflectionRead ∧ PkgSig bundle exported pkg ∧
                      PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet extensionRoute reflectionRoute reflectionPkg
  rcases packet with
    ⟨_sourceUnary, _completionObjectUnary, unitUnary, _counitUnary, idempotentUnary,
      extensionUnary, reflectionUnary, _transportUnary, _componentTransportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, sourceUnitCont,
      completionCounitCont, idempotentExtensionCont, _componentReplayCont,
      _provenanceNameCont, exportedPkg⟩
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed unitUnary extensionUnary extensionRoute
  have reflectionReadUnary : UnaryHistory reflectionRead :=
    unary_cont_closed extensionUnary reflectionUnary reflectionRoute
  exact
    ⟨idempotentUnary, extensionUnary, reflectionUnary, extensionReadUnary,
      reflectionReadUnary, sourceUnitCont, completionCounitCont, idempotentExtensionCont,
      extensionRoute, reflectionRoute, exportedPkg, reflectionPkg⟩

end BEDC.Derived.CauchyCompletionReflectorUp
