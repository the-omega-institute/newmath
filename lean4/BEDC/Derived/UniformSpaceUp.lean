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
    UniformSpacePacket point entourage diagonal refinement symmetry composition provenance name
        pointRoute ledger endpoint bundle pkg ->
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
                              UniformSpacePacket point' entourage' diagonal' refinement'
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

end BEDC.Derived.UniformSpaceUp
