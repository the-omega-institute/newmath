import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.RussellBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def RussellBoundaryCarrier [AskSetup] [PackageSetup]
    (source relation description classifier bridge descent transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory relation ∧ UnaryHistory description ∧
    UnaryHistory classifier ∧ UnaryHistory bridge ∧ UnaryHistory descent ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont source relation description ∧
          Cont classifier bridge descent ∧ Cont transport route provenance ∧
            PkgSig bundle localCert pkg

theorem RussellBoundaryCarrier_fivefold_obligations
    [AskSetup] [PackageSetup]
    {source relation description classifier bridge descent transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RussellBoundaryCarrier source relation description classifier bridge descent transport route
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RussellBoundaryCarrier source relation description classifier bridge descent transport
            route provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          Cont source relation description ∧ Cont classifier bridge descent ∧
            Cont transport route provenance ∧ hsame row localCert)
        (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _relationUnary, _descriptionUnary, _classifierUnary, _bridgeUnary,
    _descentUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    sourceRelationDescription, classifierBridgeDescent, transportRouteProvenance,
    localCertPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          RussellBoundaryCarrier source relation description classifier bridge descent transport
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
  exact {
    core := certCore
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRelationDescription, classifierBridgeDescent, transportRouteProvenance,
          sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨localCertPkg, sourceRow.right⟩
  }

theorem RussellBoundaryCarrier_namecert_noncollapse
    [AskSetup] [PackageSetup]
    {source relation description classifier classifier' bridge bridge' descent descent'
      transport route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RussellBoundaryCarrier source relation description classifier bridge descent transport route
        provenance localCert bundle pkg ->
      hsame classifier classifier' ->
        hsame bridge bridge' ->
          hsame descent descent' ->
            UnaryHistory classifier' ∧ UnaryHistory bridge' ∧ UnaryHistory descent' ∧
              Cont classifier' bridge' descent' ∧
                SemanticNameCert
                  (fun row : BHist =>
                    RussellBoundaryCarrier source relation description classifier bridge descent
                      transport route provenance localCert bundle pkg ∧ hsame row localCert)
                  (fun row : BHist =>
                    Cont source relation description ∧ Cont classifier bridge descent ∧
                      Cont transport route provenance ∧ hsame row localCert)
                  (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
                  hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier sameClassifier sameBridge sameDescent
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _relationUnary, _descriptionUnary, classifierUnary, bridgeUnary,
    descentUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _sourceRelationDescription, classifierBridgeDescent, _transportRouteProvenance,
    _localCertPkg⟩ := carrier
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have bridgeUnary' : UnaryHistory bridge' :=
    unary_transport bridgeUnary sameBridge
  have descentUnary' : UnaryHistory descent' :=
    unary_transport descentUnary sameDescent
  have classifierBridgeDescent' : Cont classifier' bridge' descent' := by
    cases sameClassifier
    cases sameBridge
    cases sameDescent
    exact classifierBridgeDescent
  exact
    ⟨classifierUnary', bridgeUnary', descentUnary', classifierBridgeDescent',
      RussellBoundaryCarrier_fivefold_obligations carrierWitness⟩

theorem RussellBoundaryCarrier_witnessed_descent_ledger
    [AskSetup] [PackageSetup]
    {source relation description classifier bridge descent transport route provenance
      localCert downward : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RussellBoundaryCarrier source relation description classifier bridge descent transport route
        provenance localCert bundle pkg ->
      Cont descent route downward ->
        PkgSig bundle downward pkg ->
          UnaryHistory descent ∧ UnaryHistory route ∧ UnaryHistory downward ∧
            Cont descent route downward ∧ PkgSig bundle localCert pkg ∧
              PkgSig bundle downward pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier descentRoute downwardPkg
  obtain ⟨_sourceUnary, _relationUnary, _descriptionUnary, _classifierUnary, _bridgeUnary,
    descentUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _sourceRelationDescription, _classifierBridgeDescent, _transportRouteProvenance,
    localCertPkg⟩ := carrier
  have downwardUnary : UnaryHistory downward :=
    unary_cont_closed descentUnary routeUnary descentRoute
  exact
    ⟨descentUnary, routeUnary, downwardUnary, descentRoute, localCertPkg, downwardPkg⟩

theorem RussellBoundaryCarrier_public_certificate
    [AskSetup] [PackageSetup]
    {source relation description classifier bridge descent transport route provenance
      localCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RussellBoundaryCarrier source relation description classifier bridge descent transport route
        provenance localCert bundle pkg ->
      Cont relation route publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              RussellBoundaryCarrier source relation description classifier bridge descent
                transport route provenance localCert bundle pkg ∧ hsame row localCert)
            (fun row : BHist =>
              Cont source relation description ∧ Cont classifier bridge descent ∧
                Cont transport route provenance ∧ hsame row localCert)
            (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
            hsame ∧
            UnaryHistory relation ∧ UnaryHistory route ∧ UnaryHistory publicRead ∧
              Cont relation route publicRead ∧ PkgSig bundle localCert pkg ∧
                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier relationRoutePublic publicPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, relationUnary, _descriptionUnary, _classifierUnary, _bridgeUnary,
    _descentUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _sourceRelationDescription, _classifierBridgeDescent, _transportRouteProvenance,
    localCertPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed relationUnary routeUnary relationRoutePublic
  exact
    ⟨RussellBoundaryCarrier_fivefold_obligations carrierWitness, relationUnary, routeUnary,
      publicUnary, relationRoutePublic, localCertPkg, publicPkg⟩

theorem RussellBoundaryCarrier_source_relation_description_transport
    [AskSetup] [PackageSetup]
    {source relation description source' relation' description' classifier bridge descent
      transport route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RussellBoundaryCarrier source relation description classifier bridge descent transport route
        provenance localCert bundle pkg ->
      hsame source source' ->
        hsame relation relation' ->
          hsame description description' ->
            UnaryHistory source' ∧ UnaryHistory relation' ∧ UnaryHistory description' ∧
              Cont source' relation' description' ∧
                SemanticNameCert
                  (fun row : BHist =>
                    RussellBoundaryCarrier source relation description classifier bridge descent
                      transport route provenance localCert bundle pkg ∧ hsame row localCert)
                  (fun row : BHist =>
                    Cont source relation description ∧ Cont classifier bridge descent ∧
                      Cont transport route provenance ∧ hsame row localCert)
                  (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
                  hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sameSource sameRelation sameDescription
  have carrierWitness := carrier
  obtain ⟨sourceUnary, relationUnary, descriptionUnary, _classifierUnary, _bridgeUnary,
    _descentUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    sourceRelationDescription, _classifierBridgeDescent, _transportRouteProvenance,
    _localCertPkg⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have relationUnary' : UnaryHistory relation' :=
    unary_transport relationUnary sameRelation
  have descriptionUnary' : UnaryHistory description' :=
    unary_transport descriptionUnary sameDescription
  have sourceRelationDescription' : Cont source' relation' description' := by
    cases sameSource
    cases sameRelation
    cases sameDescription
    exact sourceRelationDescription
  exact
    ⟨sourceUnary', relationUnary', descriptionUnary', sourceRelationDescription',
      RussellBoundaryCarrier_fivefold_obligations carrierWitness⟩

end BEDC.Derived.RussellBoundaryUp
