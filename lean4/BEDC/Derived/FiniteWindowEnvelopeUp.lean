import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWindowEnvelopeCarrier [AskSetup] [PackageSetup]
    (source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory anchor ∧ UnaryHistory window ∧ UnaryHistory ledger ∧
    UnaryHistory endpoint ∧ UnaryHistory localCert ∧ Cont window ledger regSeal ∧
      Cont regSeal endpoint streamSeal ∧ Cont streamSeal localCert provenance ∧
        PkgSig bundle provenance pkg

theorem FiniteWindowEnvelopeCarrier_regseqrat_seal_handoff [AskSetup] [PackageSetup]
    {source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeCarrier source anchor window ledger streamSeal regSeal endpoint provenance
        localCert bundle pkg →
      UnaryHistory regSeal ∧ hsame regSeal (append window ledger) ∧
        PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_sourceUnary, _anchorUnary, windowUnary, ledgerUnary, _endpointUnary,
    _localCertUnary, regSealCont, _streamSealCont, _provenanceCont, provenancePkg⟩ := carrier
  have regSealUnary : UnaryHistory regSeal :=
    unary_cont_closed windowUnary ledgerUnary regSealCont
  have regSealSame : hsame regSeal (append window ledger) :=
    regSealCont
  exact And.intro regSealUnary (And.intro regSealSame provenancePkg)

theorem FiniteWindowEnvelopeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeCarrier source anchor window ledger streamSeal regSeal endpoint provenance
        localCert bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          UnaryHistory source ∧ UnaryHistory anchor ∧ UnaryHistory window ∧
            UnaryHistory ledger ∧ UnaryHistory row)
        (fun row : BHist => Cont streamSeal localCert row ∧ PkgSig bundle row pkg)
        (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨sourceUnary, anchorUnary, windowUnary, ledgerUnary, endpointUnary,
    localCertUnary, regSealCont, streamSealCont, provenanceCont, provenancePkg⟩ := carrier
  have regSealUnary : UnaryHistory regSeal :=
    unary_cont_closed windowUnary ledgerUnary regSealCont
  have streamSealUnary : UnaryHistory streamSeal :=
    unary_cont_closed regSealUnary endpointUnary streamSealCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed streamSealUnary localCertUnary provenanceCont
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, provenancePkg⟩
      equiv_refl := by
        intro row source
        exact ⟨source.right, hsame_refl row⟩
      equiv_symm := by
        intro row _other classified
        cases classified.right
        exact ⟨classified.left, hsame_refl row⟩
      equiv_trans := by
        intro _row _middle _other leftClassified rightClassified
        exact
          ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _other classified source
        cases classified.right
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨sourceUnary, anchorUnary, windowUnary, ledgerUnary,
          unary_transport provenanceUnary (hsame_symm source.left)⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨provenanceCont, source.right⟩
  }

def FiniteWindowEnvelopeBHistCarrier [AskSetup] [PackageSetup]
    (source anchor window ledger streamClass sealRow endpoint provenance nameCert route : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory anchor ∧ UnaryHistory window ∧
    UnaryHistory ledger ∧ UnaryHistory streamClass ∧ UnaryHistory sealRow ∧
      UnaryHistory endpoint ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        UnaryHistory route ∧ hsame sealRow (append ledger streamClass) ∧
          Cont sealRow endpoint route ∧ PkgSig bundle endpoint pkg

theorem FiniteWindowEnvelopeBHistCarrier_regseqrat_seal_handoff [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route source'
      anchor' window' ledger' endpoint' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg ->
      hsame source source' ->
        hsame anchor anchor' ->
          hsame window window' ->
            hsame ledger ledger' ->
              hsame endpoint endpoint' ->
                hsame provenance provenance' ->
                  hsame nameCert nameCert' ->
                    exists streamClass' sealOut route',
                      FiniteWindowEnvelopeBHistCarrier source' anchor' window' ledger'
                          streamClass' sealOut endpoint' provenance' nameCert' route'
                          bundle pkg ∧
                        hsame sealOut (append ledger' streamClass') ∧
                          Cont sealOut endpoint' route' := by
  intro carrier sameSource sameAnchor sameWindow sameLedger sameEndpoint sameProvenance
    sameNameCert
  obtain ⟨sourceUnary, anchorUnary, windowUnary, ledgerUnary, streamClassUnary, _sealUnary,
    endpointUnary, provenanceUnary, nameCertUnary, _routeUnary, _sealEq, _routeRow,
    pkgRow⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have anchorUnary' : UnaryHistory anchor' :=
    unary_transport anchorUnary sameAnchor
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  let streamClass' : BHist := streamClass
  let sealOut : BHist := append ledger' streamClass'
  let route' : BHist := append sealOut endpoint'
  have sealUnary' : UnaryHistory sealOut :=
    unary_cont_closed ledgerUnary' streamClassUnary (rfl : Cont ledger' streamClass' sealOut)
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed sealUnary' endpointUnary' (rfl : Cont sealOut endpoint' route')
  have pkgRow' : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact pkgRow
  exact
    ⟨streamClass', sealOut, route',
      ⟨sourceUnary', anchorUnary', windowUnary', ledgerUnary', streamClassUnary, sealUnary',
        endpointUnary', provenanceUnary', nameCertUnary', routeUnary', rfl, rfl, pkgRow'⟩,
      rfl, rfl⟩

theorem FiniteWindowEnvelopeBHistCarrier_realup_window_exactness [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route endpointRead
      endpointRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg ->
      Cont route endpoint endpointRead ->
        Cont endpointRead provenance endpointRoute ->
          UnaryHistory endpointRead ∧ UnaryHistory endpointRoute ∧
            hsame sealRow (append ledger streamClass) ∧ Cont sealRow endpoint route ∧
              PkgSig bundle endpoint pkg := by
  intro carrier readStep provenanceStep
  obtain ⟨_sourceUnary, _anchorUnary, _windowUnary, _ledgerUnary, _streamClassUnary,
    _sealUnary, endpointUnary, provenanceUnary, _nameCertUnary, routeUnary, sealEq,
    routeRow, pkgRow⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed routeUnary endpointUnary readStep
  have endpointRouteUnary : UnaryHistory endpointRoute :=
    unary_cont_closed endpointReadUnary provenanceUnary provenanceStep
  exact ⟨endpointReadUnary, endpointRouteUnary, sealEq, routeRow, pkgRow⟩

theorem FiniteWindowEnvelopeBHistCarrier_streamname_regseqrat_scope [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route
      endpointRead endpointRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg →
      Cont route endpoint endpointRead →
        Cont endpointRead provenance endpointRoute →
          UnaryHistory window ∧ UnaryHistory ledger ∧ UnaryHistory sealRow ∧
            UnaryHistory endpointRead ∧ UnaryHistory endpointRoute ∧
              hsame sealRow (append ledger streamClass) ∧ Cont sealRow endpoint route ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier readStep provenanceStep
  obtain ⟨_sourceUnary, _anchorUnary, windowUnary, ledgerUnary, _streamClassUnary,
    sealRowUnary, endpointUnary, provenanceUnary, _nameCertUnary, routeUnary, sealEq,
    routeRow, pkgRow⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed routeUnary endpointUnary readStep
  have endpointRouteUnary : UnaryHistory endpointRoute :=
    unary_cont_closed endpointReadUnary provenanceUnary provenanceStep
  exact ⟨windowUnary, ledgerUnary, sealRowUnary, endpointReadUnary, endpointRouteUnary,
    sealEq, routeRow, pkgRow⟩

theorem FiniteWindowEnvelopeBHistCarrier_endpoint_source_determinacy [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route endpointRead
      endpointRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg ->
      Cont route endpoint endpointRead ->
        Cont endpointRead provenance endpointRoute ->
          UnaryHistory window ∧ UnaryHistory ledger ∧ UnaryHistory sealRow ∧
            UnaryHistory endpoint ∧ UnaryHistory endpointRead ∧ UnaryHistory endpointRoute ∧
              hsame sealRow (append ledger streamClass) ∧ Cont sealRow endpoint route ∧
                Cont route endpoint endpointRead ∧
                  Cont endpointRead provenance endpointRoute ∧ PkgSig bundle endpoint pkg := by
  intro carrier readStep provenanceStep
  obtain ⟨_sourceUnary, _anchorUnary, windowUnary, ledgerUnary, _streamClassUnary,
    sealRowUnary, endpointUnary, provenanceUnary, _nameCertUnary, routeUnary, sealEq,
    routeRow, pkgRow⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed routeUnary endpointUnary readStep
  have endpointRouteUnary : UnaryHistory endpointRoute :=
    unary_cont_closed endpointReadUnary provenanceUnary provenanceStep
  exact
    ⟨windowUnary, ledgerUnary, sealRowUnary, endpointUnary, endpointReadUnary,
      endpointRouteUnary, sealEq, routeRow, readStep, provenanceStep, pkgRow⟩

theorem FiniteWindowEnvelopeBHistCarrier_common_refinement_exactness [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route source'
      anchor' window' ledger' endpoint' provenance' nameCert' endpointRead endpointRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg ->
      hsame source source' ->
        hsame anchor anchor' ->
          hsame window window' ->
            hsame ledger ledger' ->
              hsame endpoint endpoint' ->
                hsame provenance provenance' ->
                  hsame nameCert nameCert' ->
                    Cont route endpoint endpointRead ->
                      Cont endpointRead provenance endpointRoute ->
                        exists streamClass' sealOut route',
                          FiniteWindowEnvelopeBHistCarrier source' anchor' window' ledger'
                              streamClass' sealOut endpoint' provenance' nameCert' route'
                              bundle pkg ∧
                            hsame sealOut (append ledger' streamClass') ∧
                              UnaryHistory endpointRead ∧ UnaryHistory endpointRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier sameSource sameAnchor sameWindow sameLedger sameEndpoint sameProvenance
    sameNameCert readStep provenanceStep
  obtain ⟨streamClass', sealOut, route', transported, sealEq, _routeRow⟩ :=
    FiniteWindowEnvelopeBHistCarrier_regseqrat_seal_handoff (bundle := bundle) (pkg := pkg)
      carrier sameSource sameAnchor sameWindow sameLedger sameEndpoint sameProvenance
      sameNameCert
  have exactRows :=
    FiniteWindowEnvelopeBHistCarrier_realup_window_exactness (bundle := bundle) (pkg := pkg)
      carrier readStep provenanceStep
  exact
    ⟨streamClass', sealOut, route', transported, sealEq, exactRows.left,
      exactRows.right.left⟩

theorem FiniteWindowEnvelopeBHistCarrier_tail_projection [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route tailRead
      tailRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg →
      Cont window ledger tailRead →
        Cont tailRead endpoint tailRoute →
          UnaryHistory tailRead ∧ UnaryHistory tailRoute ∧ UnaryHistory window ∧
            UnaryHistory ledger ∧ hsame sealRow (append ledger streamClass) ∧
              Cont sealRow endpoint route ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier tailReadStep tailRouteStep
  obtain ⟨_sourceUnary, _anchorUnary, windowUnary, ledgerUnary, _streamClassUnary,
    _sealRowUnary, endpointUnary, _provenanceUnary, _nameCertUnary, _routeUnary, sealEq,
    routeRow, pkgRow⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary ledgerUnary tailReadStep
  have tailRouteUnary : UnaryHistory tailRoute :=
    unary_cont_closed tailReadUnary endpointUnary tailRouteStep
  exact
    ⟨tailReadUnary, tailRouteUnary, windowUnary, ledgerUnary, sealEq, routeRow, pkgRow⟩

theorem FiniteWindowEnvelopeUp_StdBridge [AskSetup] [PackageSetup]
    {source anchor window ledger streamClass sealRow endpoint provenance nameCert route endpointRead
      endpointRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeBHistCarrier source anchor window ledger streamClass sealRow endpoint
        provenance nameCert route bundle pkg ->
      Cont route endpoint endpointRead ->
        Cont endpointRead provenance endpointRoute ->
          SemanticNameCert
              (fun row : BHist => hsame row route ∧ UnaryHistory row ∧ PkgSig bundle endpoint pkg)
              (fun row : BHist =>
                UnaryHistory window ∧ UnaryHistory ledger ∧
                  hsame sealRow (append ledger streamClass) ∧ Cont sealRow endpoint row)
              (fun row : BHist => PkgSig bundle endpoint pkg ∧ Cont sealRow endpoint row)
              (fun row row' : BHist => PkgSig bundle endpoint pkg ∧ hsame row row') ∧
            UnaryHistory endpointRead ∧ UnaryHistory endpointRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier readStep provenanceStep
  obtain ⟨_sourceUnary, _anchorUnary, windowUnary, ledgerUnary, _streamClassUnary,
    _sealUnary, endpointUnary, provenanceUnary, _nameCertUnary, routeUnary, sealEq, routeRow,
    endpointPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed routeUnary endpointUnary readStep
  have endpointRouteUnary : UnaryHistory endpointRoute :=
    unary_cont_closed endpointReadUnary provenanceUnary provenanceStep
  have sourceAtRoute :
      hsame route route ∧ UnaryHistory route ∧ PkgSig bundle endpoint pkg :=
    ⟨hsame_refl route, routeUnary, endpointPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row route ∧ UnaryHistory row ∧ PkgSig bundle endpoint pkg)
          (fun row : BHist =>
            UnaryHistory window ∧ UnaryHistory ledger ∧
              hsame sealRow (append ledger streamClass) ∧ Cont sealRow endpoint row)
          (fun row : BHist => PkgSig bundle endpoint pkg ∧ Cont sealRow endpoint row)
          (fun row row' : BHist => PkgSig bundle endpoint pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro route sourceAtRoute
      equiv_refl := by
        intro row _source
        exact ⟨endpointPkg, hsame_refl row⟩
      equiv_symm := by
        intro row _other classified
        cases classified.right
        exact ⟨classified.left, hsame_refl row⟩
      equiv_trans := by
        intro _row _middle _other leftClassified rightClassified
        exact
          ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _other classified source
        cases classified.right
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact ⟨windowUnary, ledgerUnary, sealEq, routeRow⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨source.right.right, routeRow⟩
  }
  exact ⟨cert, endpointReadUnary, endpointRouteUnary⟩

end BEDC.Derived.FiniteWindowEnvelopeUp
