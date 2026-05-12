import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformSpacePacket [AskSetup] [PackageSetup]
    (point entourage diagonal refinement symmetry composition transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory point ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
    UnaryHistory refinement ∧ UnaryHistory symmetry ∧ UnaryHistory composition ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont point entourage diagonal ∧ Cont diagonal refinement symmetry ∧
          Cont symmetry composition transport ∧ Cont transport provenance name ∧
            PkgSig bundle name pkg

theorem UniformSpacePacket_filterbase_diagonal_obligation [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition transport provenance name
      filterbase : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpacePacket point entourage diagonal refinement symmetry composition transport provenance
        name bundle pkg ->
      Cont diagonal refinement filterbase ->
        PkgSig bundle filterbase pkg ->
          UnaryHistory point ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
            UnaryHistory refinement ∧ UnaryHistory filterbase ∧
              Cont point entourage diagonal ∧ Cont diagonal refinement filterbase ∧
                PkgSig bundle filterbase pkg := by
  intro packet diagonalRefinementFilterbase filterbasePkg
  obtain ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, _symmetryUnary,
    _compositionUnary, _transportUnary, _provenanceUnary, _nameUnary, pointEntourageDiagonal,
    _diagonalRefinementSymmetry, _symmetryCompositionTransport, _transportProvenanceName,
    _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbase :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinementFilterbase
  exact
    ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, filterbaseUnary,
      pointEntourageDiagonal, diagonalRefinementFilterbase, filterbasePkg⟩

theorem UniformSpacePacket_common_refinement_functoriality [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition transport provenance name
      route01 route12 route02 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpacePacket point entourage diagonal refinement symmetry composition transport provenance
        name bundle pkg ->
      Cont diagonal refinement route01 ->
        Cont route01 symmetry route12 ->
          Cont route12 composition route02 ->
            PkgSig bundle route02 pkg ->
              UnaryHistory route01 ∧ UnaryHistory route12 ∧ UnaryHistory route02 ∧
                Cont diagonal refinement route01 ∧ Cont route01 symmetry route12 ∧
                  Cont route12 composition route02 ∧ PkgSig bundle route02 pkg ∧
                    PkgSig bundle name pkg := by
  intro packet diagonalRefinementRoute routeSymmetry routeComposition routePkg
  obtain ⟨_pointUnary, _entourageUnary, diagonalUnary, refinementUnary, symmetryUnary,
    compositionUnary, _transportUnary, _provenanceUnary, _nameUnary,
    _pointEntourageDiagonal, _diagonalRefinementSymmetry, _symmetryCompositionTransport,
    _transportProvenanceName, namePkg⟩ := packet
  have route01Unary : UnaryHistory route01 :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinementRoute
  have route12Unary : UnaryHistory route12 :=
    unary_cont_closed route01Unary symmetryUnary routeSymmetry
  have route02Unary : UnaryHistory route02 :=
    unary_cont_closed route12Unary compositionUnary routeComposition
  exact
    ⟨route01Unary, route12Unary, route02Unary, diagonalRefinementRoute, routeSymmetry,
      routeComposition, routePkg, namePkg⟩

theorem UniformSpacePacket_symmetry_composition_obligation [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition transport provenance name
      symmetryRead compositionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpacePacket point entourage diagonal refinement symmetry composition transport provenance
        name bundle pkg ->
      Cont diagonal refinement symmetryRead ->
        Cont symmetryRead composition compositionRead ->
          PkgSig bundle compositionRead pkg ->
            UnaryHistory symmetryRead ∧ UnaryHistory compositionRead ∧
              Cont diagonal refinement symmetryRead ∧
                Cont symmetryRead composition compositionRead ∧
                  PkgSig bundle compositionRead pkg ∧ PkgSig bundle name pkg := by
  intro packet diagonalRefinementSymmetryRead symmetryCompositionRead compositionReadPkg
  obtain ⟨_pointUnary, _entourageUnary, diagonalUnary, refinementUnary, _symmetryUnary,
    compositionUnary, _transportUnary, _provenanceUnary, _nameUnary, _pointEntourageDiagonal,
    _diagonalRefinementSymmetry, _symmetryCompositionTransport, _transportProvenanceName,
    namePkg⟩ := packet
  have symmetryReadUnary : UnaryHistory symmetryRead :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinementSymmetryRead
  have compositionReadUnary : UnaryHistory compositionRead :=
    unary_cont_closed symmetryReadUnary compositionUnary symmetryCompositionRead
  exact
    ⟨symmetryReadUnary, compositionReadUnary, diagonalRefinementSymmetryRead,
      symmetryCompositionRead, compositionReadPkg, namePkg⟩

def UniformSpaceEntouragePacket [AskSetup] [PackageSetup]
    (base entourage diagonal symmetry composition provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory base ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
    UnaryHistory symmetry ∧ UnaryHistory composition ∧ Cont base entourage diagonal ∧
      Cont diagonal symmetry composition ∧ Cont composition provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem UniformSpaceEntouragePacket_diagonal_refinement_obligation [AskSetup] [PackageSetup]
    {base entourage diagonal symmetry composition provenance endpoint refinement refinedEndpoint :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpaceEntouragePacket base entourage diagonal symmetry composition provenance endpoint
        bundle pkg ->
      UnaryHistory refinement ->
        Cont diagonal refinement refinedEndpoint ->
          PkgSig bundle refinedEndpoint pkg ->
            UnaryHistory base ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
              UnaryHistory refinement ∧ UnaryHistory refinedEndpoint ∧
                Cont base entourage diagonal ∧ Cont diagonal refinement refinedEndpoint ∧
                  PkgSig bundle refinedEndpoint pkg := by
  intro packet refinementUnary diagonalRefinement refinedPkg
  obtain ⟨baseUnary, entourageUnary, diagonalUnary, _symmetryUnary, _compositionUnary,
    baseEntourageDiagonal, _diagonalSymmetryComposition, _compositionProvenanceEndpoint,
    _endpointPkg⟩ := packet
  have refinedEndpointUnary : UnaryHistory refinedEndpoint :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinement
  exact
    ⟨baseUnary, entourageUnary, diagonalUnary, refinementUnary, refinedEndpointUnary,
      baseEntourageDiagonal, diagonalRefinement, refinedPkg⟩

def UniformSpaceClassifierPacket [AskSetup] [PackageSetup]
    (point entourage diagonal refinement symmetry composition provenance name pointRoute ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory point ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
    UnaryHistory refinement ∧ UnaryHistory symmetry ∧ UnaryHistory composition ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont point entourage pointRoute ∧
        Cont diagonal refinement ledger ∧ Cont symmetry composition endpoint ∧
          PkgSig bundle endpoint pkg

theorem UniformSpacePacket_classifier_transport_obligation [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition provenance name pointRoute ledger
      endpoint point' entourage' diagonal' refinement' symmetry' composition' provenance' name'
      pointRoute' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpaceClassifierPacket point entourage diagonal refinement symmetry composition provenance
        name pointRoute ledger endpoint bundle pkg ->
      hsame point point' ->
        hsame entourage entourage' ->
          hsame diagonal diagonal' ->
            hsame refinement refinement' ->
              hsame symmetry symmetry' ->
                hsame composition composition' ->
                  hsame provenance provenance' ->
                    hsame name name' ->
                      Cont point' entourage' pointRoute' ->
                        Cont diagonal' refinement' ledger' ->
                          Cont symmetry' composition' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              UniformSpaceClassifierPacket point' entourage' diagonal' refinement'
                                  symmetry' composition' provenance' name' pointRoute' ledger'
                                  endpoint' bundle pkg ∧
                                hsame pointRoute pointRoute' ∧ hsame ledger ledger' ∧
                                  hsame endpoint endpoint' := by
  intro packet samePoint sameEntourage sameDiagonal sameRefinement sameSymmetry
    sameComposition sameProvenance sameName pointEntouragePointRoute'
    diagonalRefinementLedger' symmetryCompositionEndpoint' endpointPkg'
  rcases packet with
    ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, symmetryUnary,
      compositionUnary, provenanceUnary, nameUnary, pointEntouragePointRoute,
      diagonalRefinementLedger, symmetryCompositionEndpoint, _endpointPkg⟩
  have samePointRoute : hsame pointRoute pointRoute' :=
    cont_respects_hsame samePoint sameEntourage pointEntouragePointRoute
      pointEntouragePointRoute'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameDiagonal sameRefinement diagonalRefinementLedger
      diagonalRefinementLedger'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSymmetry sameComposition symmetryCompositionEndpoint
      symmetryCompositionEndpoint'
  have pointUnary' : UnaryHistory point' := unary_transport pointUnary samePoint
  have entourageUnary' : UnaryHistory entourage' :=
    unary_transport entourageUnary sameEntourage
  have diagonalUnary' : UnaryHistory diagonal' := unary_transport diagonalUnary sameDiagonal
  have refinementUnary' : UnaryHistory refinement' :=
    unary_transport refinementUnary sameRefinement
  have symmetryUnary' : UnaryHistory symmetry' := unary_transport symmetryUnary sameSymmetry
  have compositionUnary' : UnaryHistory composition' :=
    unary_transport compositionUnary sameComposition
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  exact
    ⟨⟨pointUnary', entourageUnary', diagonalUnary', refinementUnary', symmetryUnary',
        compositionUnary', provenanceUnary', nameUnary', pointEntouragePointRoute',
        diagonalRefinementLedger', symmetryCompositionEndpoint', endpointPkg'⟩,
      samePointRoute, sameLedger, sameEndpoint⟩

theorem UniformSpacePacket_scoped_entourage_package [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition transport provenance name filterbase
      cauchy completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpacePacket point entourage diagonal refinement symmetry composition transport provenance
        name bundle pkg ->
      Cont diagonal refinement filterbase ->
        Cont filterbase transport cauchy ->
          Cont cauchy provenance completion ->
            PkgSig bundle completion pkg ->
              UnaryHistory point ∧ UnaryHistory entourage ∧ UnaryHistory filterbase ∧
                UnaryHistory cauchy ∧ UnaryHistory completion ∧ Cont point entourage diagonal ∧
                  Cont diagonal refinement filterbase ∧ Cont filterbase transport cauchy ∧
                    Cont cauchy provenance completion ∧ PkgSig bundle completion pkg := by
  intro packet diagonalRefinementFilterbase filterbaseTransportCauchy
    cauchyProvenanceCompletion completionPkg
  obtain ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, _symmetryUnary,
    _compositionUnary, transportUnary, provenanceUnary, _nameUnary, pointEntourageDiagonal,
    _diagonalRefinementSymmetry, _symmetryCompositionTransport, _transportProvenanceName,
    _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbase :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinementFilterbase
  have cauchyUnary : UnaryHistory cauchy :=
    unary_cont_closed filterbaseUnary transportUnary filterbaseTransportCauchy
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed cauchyUnary provenanceUnary cauchyProvenanceCompletion
  exact
    ⟨pointUnary, entourageUnary, filterbaseUnary, cauchyUnary, completionUnary,
      pointEntourageDiagonal, diagonalRefinementFilterbase, filterbaseTransportCauchy,
      cauchyProvenanceCompletion, completionPkg⟩

theorem UniformSpaceClassifierPacket_cauchy_completion_handoff [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition provenance name pointRoute ledger
      endpoint handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpaceClassifierPacket point entourage diagonal refinement symmetry composition provenance
        name pointRoute ledger endpoint bundle pkg ->
      Cont endpoint provenance handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory pointRoute ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            UnaryHistory handoff ∧ Cont point entourage pointRoute ∧
              Cont diagonal refinement ledger ∧ Cont symmetry composition endpoint ∧
                Cont endpoint provenance handoff ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle handoff pkg := by
  intro packet endpointProvenanceHandoff handoffPkg
  rcases packet with
    ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, symmetryUnary,
      compositionUnary, provenanceUnary, _nameUnary, pointEntouragePointRoute,
      diagonalRefinementLedger, symmetryCompositionEndpoint, endpointPkg⟩
  have pointRouteUnary : UnaryHistory pointRoute :=
    unary_cont_closed pointUnary entourageUnary pointEntouragePointRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinementLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed symmetryUnary compositionUnary symmetryCompositionEndpoint
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed endpointUnary provenanceUnary endpointProvenanceHandoff
  exact
    ⟨pointRouteUnary, ledgerUnary, endpointUnary, handoffUnary, pointEntouragePointRoute,
      diagonalRefinementLedger, symmetryCompositionEndpoint, endpointProvenanceHandoff,
      endpointPkg, handoffPkg⟩

end BEDC.Derived.UniformSpaceUp
