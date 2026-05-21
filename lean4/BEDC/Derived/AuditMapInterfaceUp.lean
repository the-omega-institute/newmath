import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapInterfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def AuditMapInterfaceCarrier [AskSetup] [PackageSetup]
    (established conditional obstruction frontier crossMap transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory established ∧ UnaryHistory conditional ∧ UnaryHistory obstruction ∧
    UnaryHistory frontier ∧ UnaryHistory crossMap ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
          Cont transport route provenance ∧ PkgSig bundle localCert pkg

theorem AuditMapInterfaceCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport
              route provenance localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
              Cont transport route provenance ∧ hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame ∧
        UnaryHistory established ∧ UnaryHistory conditional ∧ UnaryHistory obstruction ∧
          UnaryHistory frontier ∧ UnaryHistory crossMap ∧ UnaryHistory transport ∧
            UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
              Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
                Cont transport route provenance ∧ PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
    transportUnary, routeUnary, provenanceUnary, localCertUnary, establishedConditionalObstruction,
    obstructionFrontierCrossMap, transportRouteProvenance, localCertPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport
            route provenance localCert bundle pkg ∧ hsame row localCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro localCert
        (And.intro carrierWitness (hsame_refl localCert))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport
              route provenance localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont established conditional obstruction ∧ Cont obstruction frontier crossMap ∧
              Cont transport route provenance ∧ hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨establishedConditionalObstruction, obstructionFrontierCrossMap,
            transportRouteProvenance, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨localCertPkg, sourceRow.right⟩
    }
  exact
    ⟨semantic, establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
      transportUnary, routeUnary, provenanceUnary, localCertUnary, establishedConditionalObstruction,
        obstructionFrontierCrossMap, transportRouteProvenance, localCertPkg⟩

theorem AuditMapInterfaceCarrier_cross_map_consumer_boundary
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance
      localCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      Cont crossMap route consumerRead ->
        PkgSig bundle consumerRead pkg ->
          UnaryHistory crossMap ∧ UnaryHistory route ∧ UnaryHistory consumerRead ∧
            Cont crossMap route consumerRead ∧ PkgSig bundle localCert pkg ∧
              PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier crossMapRoute consumerPkg
  obtain ⟨_establishedUnary, _conditionalUnary, _obstructionUnary, _frontierUnary,
    crossMapUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    _transportRouteProvenance, localCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed crossMapUnary routeUnary crossMapRoute
  exact
    ⟨crossMapUnary, routeUnary, consumerUnary, crossMapRoute, localCertPkg, consumerPkg⟩

theorem AuditMapInterfaceCarrier_conditional_row_discharge_boundary
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance localCert
      conditionalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      Cont conditional route conditionalRead ->
        UnaryHistory established ∧ UnaryHistory conditional ∧ UnaryHistory route ∧
          UnaryHistory conditionalRead ∧ Cont conditional route conditionalRead ∧
            PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier conditionalRoute
  obtain ⟨establishedUnary, conditionalUnary, _obstructionUnary, _frontierUnary,
    _crossMapUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    _transportRouteProvenance, localCertPkg⟩ := carrier
  have conditionalReadUnary : UnaryHistory conditionalRead :=
    unary_cont_closed conditionalUnary routeUnary conditionalRoute
  exact
    ⟨establishedUnary, conditionalUnary, routeUnary, conditionalReadUnary,
      conditionalRoute, localCertPkg⟩

theorem AuditMapInterfaceCarrier_obstruction_row_nonescape
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance localCert
      obstructionRead obstructionPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      Cont obstruction route obstructionRead ->
        hsame obstruction obstructionPrime ->
          UnaryHistory obstruction ∧ UnaryHistory route ∧ UnaryHistory obstructionRead ∧
            hsame obstruction obstructionPrime ∧ Cont obstructionPrime route obstructionRead ∧
              PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier obstructionRoute obstructionSame
  obtain ⟨_establishedUnary, _conditionalUnary, obstructionUnary, _frontierUnary,
    _crossMapUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    _transportRouteProvenance, localCertPkg⟩ := carrier
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary routeUnary obstructionRoute
  cases obstructionSame
  exact
    ⟨obstructionUnary, routeUnary, obstructionReadUnary, hsame_refl obstruction,
      obstructionRoute, localCertPkg⟩

theorem AuditMapInterfaceCarrier_route_readback_totality
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance localCert
      establishedRead conditionalRead obstructionRead frontierRead crossMapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      Cont established route establishedRead ->
        Cont conditional route conditionalRead ->
          Cont obstruction route obstructionRead ->
            Cont frontier route frontierRead ->
              Cont crossMap route crossMapRead ->
                PkgSig bundle establishedRead pkg ->
                  PkgSig bundle conditionalRead pkg ->
                    PkgSig bundle obstructionRead pkg ->
                      PkgSig bundle frontierRead pkg ->
                        PkgSig bundle crossMapRead pkg ->
                          UnaryHistory establishedRead ∧ UnaryHistory conditionalRead ∧
                            UnaryHistory obstructionRead ∧ UnaryHistory frontierRead ∧
                              UnaryHistory crossMapRead ∧ PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier establishedRoute conditionalRoute obstructionRoute frontierRoute crossMapRoute
    _establishedPkg _conditionalPkg _obstructionPkg _frontierPkg _crossMapPkg
  obtain ⟨establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    _transportRouteProvenance, localCertPkg⟩ := carrier
  have establishedReadUnary : UnaryHistory establishedRead :=
    unary_cont_closed establishedUnary routeUnary establishedRoute
  have conditionalReadUnary : UnaryHistory conditionalRead :=
    unary_cont_closed conditionalUnary routeUnary conditionalRoute
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary routeUnary obstructionRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed frontierUnary routeUnary frontierRoute
  have crossMapReadUnary : UnaryHistory crossMapRead :=
    unary_cont_closed crossMapUnary routeUnary crossMapRoute
  exact
    ⟨establishedReadUnary, conditionalReadUnary, obstructionReadUnary, frontierReadUnary,
      crossMapReadUnary, localCertPkg⟩

theorem AuditMapInterfaceCarrier_template_instantiation_boundary
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance localCert
      templateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      Cont provenance route templateRead ->
        PkgSig bundle templateRead pkg ->
          UnaryHistory established ∧ UnaryHistory conditional ∧ UnaryHistory obstruction ∧
            UnaryHistory frontier ∧ UnaryHistory crossMap ∧ UnaryHistory provenance ∧
              UnaryHistory route ∧ UnaryHistory templateRead ∧
                Cont provenance route templateRead ∧ PkgSig bundle localCert pkg ∧
                  PkgSig bundle templateRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier provenanceRoute templatePkg
  obtain ⟨establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
    _transportUnary, routeUnary, provenanceUnary, _localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    _transportRouteProvenance, localCertPkg⟩ := carrier
  have templateReadUnary : UnaryHistory templateRead :=
    unary_cont_closed provenanceUnary routeUnary provenanceRoute
  exact
    ⟨establishedUnary, conditionalUnary, obstructionUnary, frontierUnary, crossMapUnary,
      provenanceUnary, routeUnary, templateReadUnary, provenanceRoute, localCertPkg, templatePkg⟩

theorem AuditMapInterfaceCarrier_frontier_consumer_transport_routing
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance localCert
      frontier' crossMap' frontierRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      hsame frontier frontier' ->
        hsame crossMap crossMap' ->
          Cont frontier' crossMap' frontierRead ->
            Cont frontierRead route consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory frontier' ∧ UnaryHistory crossMap' ∧ UnaryHistory route ∧
                  UnaryHistory frontierRead ∧ UnaryHistory consumerRead ∧
                    hsame frontier frontier' ∧ hsame crossMap crossMap' ∧
                      Cont frontier' crossMap' frontierRead ∧
                        Cont frontierRead route consumerRead ∧
                          Cont transport route provenance ∧ PkgSig bundle localCert pkg ∧
                            PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier sameFrontier sameCrossMap frontierCrossMap consumerRoute consumerPkg
  obtain ⟨_establishedUnary, _conditionalUnary, _obstructionUnary, frontierUnary,
    crossMapUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    transportRouteProvenance, localCertPkg⟩ := carrier
  have frontierUnary' : UnaryHistory frontier' := unary_transport frontierUnary sameFrontier
  have crossMapUnary' : UnaryHistory crossMap' := unary_transport crossMapUnary sameCrossMap
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed frontierUnary' crossMapUnary' frontierCrossMap
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed frontierReadUnary routeUnary consumerRoute
  exact
    ⟨frontierUnary', crossMapUnary', routeUnary, frontierReadUnary, consumerReadUnary,
      sameFrontier, sameCrossMap, frontierCrossMap, consumerRoute, transportRouteProvenance,
      localCertPkg, consumerPkg⟩

theorem AuditMapInterfaceCarrier_route_readback_transport_totality
    [AskSetup] [PackageSetup]
    {established conditional obstruction frontier crossMap transport route provenance localCert
      route' localCert' routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapInterfaceCarrier established conditional obstruction frontier crossMap transport route
        provenance localCert bundle pkg ->
      hsame route route' ->
        hsame localCert localCert' ->
          Cont route' localCert' routeRead ->
            PkgSig bundle routeRead pkg ->
              UnaryHistory route' ∧ UnaryHistory localCert' ∧ UnaryHistory routeRead ∧
                hsame route route' ∧ hsame localCert localCert' ∧
                  Cont transport route provenance ∧ Cont route' localCert' routeRead ∧
                    PkgSig bundle localCert pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier sameRoute sameLocalCert routeLocalCert routeReadPkg
  obtain ⟨_establishedUnary, _conditionalUnary, _obstructionUnary, _frontierUnary,
    _crossMapUnary, _transportUnary, routeUnary, _provenanceUnary, localCertUnary,
    _establishedConditionalObstruction, _obstructionFrontierCrossMap,
    transportRouteProvenance, localCertPkg⟩ := carrier
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed routeUnary' localCertUnary' routeLocalCert
  exact
    ⟨routeUnary', localCertUnary', routeReadUnary, sameRoute, sameLocalCert,
      transportRouteProvenance, routeLocalCert, localCertPkg, routeReadPkg⟩

end BEDC.Derived.AuditMapInterfaceUp
