import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TriangulatedCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TriangulatedCatFiniteCarrier [AskSetup] [PackageSetup]
    (category derived shift triangle morphism classifier contRows provenance endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory derived ∧ UnaryHistory shift ∧
    UnaryHistory triangle ∧ UnaryHistory morphism ∧ UnaryHistory classifier ∧
      UnaryHistory contRows ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont category derived shift ∧ Cont shift triangle morphism ∧
          Cont morphism classifier contRows ∧ Cont contRows provenance endpoint ∧
            PkgSig probe endpoint pkg

theorem TriangulatedCatFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {category derived shift triangle morphism classifier contRows provenance endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
        contRows provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
              contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
              contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
              contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          hsame ∧
        Cont category derived shift ∧ Cont shift triangle morphism ∧
          Cont morphism classifier contRows ∧ Cont contRows provenance endpoint ∧
            PkgSig probe endpoint pkg := by
  intro carrier
  cases carrier with
  | intro categoryUnary rest =>
      cases rest with
      | intro derivedUnary rest =>
          cases rest with
          | intro shiftUnary rest =>
              cases rest with
              | intro triangleUnary rest =>
                  cases rest with
                  | intro morphismUnary rest =>
                      cases rest with
                      | intro classifierUnary rest =>
                          cases rest with
                          | intro contRowsUnary rest =>
                              cases rest with
                              | intro provenanceUnary rest =>
                                  cases rest with
                                  | intro endpointUnary rest =>
                                      cases rest with
                                      | intro categoryDerivedShift rest =>
                                          cases rest with
                                          | intro shiftTriangleMorphism rest =>
                                              cases rest with
                                              | intro morphismClassifierRows rest =>
                                                  cases rest with
                                                  | intro rowsProvenanceEndpoint pkgSig =>
                                                      have carrierAgain :
                                                          TriangulatedCatFiniteCarrier category
                                                            derived shift triangle morphism
                                                            classifier contRows provenance
                                                            endpoint probe pkg :=
                                                        ⟨categoryUnary, derivedUnary, shiftUnary,
                                                          triangleUnary, morphismUnary,
                                                          classifierUnary, contRowsUnary,
                                                          provenanceUnary, endpointUnary,
                                                          categoryDerivedShift,
                                                          shiftTriangleMorphism,
                                                          morphismClassifierRows,
                                                          rowsProvenanceEndpoint, pkgSig⟩
                                                      have cert :
                                                          SemanticNameCert
                                                            (fun row : BHist =>
                                                              TriangulatedCatFiniteCarrier
                                                                category derived shift triangle
                                                                morphism classifier contRows
                                                                provenance endpoint probe pkg ∧
                                                                hsame row endpoint)
                                                            (fun row : BHist =>
                                                              TriangulatedCatFiniteCarrier
                                                                category derived shift triangle
                                                                morphism classifier contRows
                                                                provenance endpoint probe pkg ∧
                                                                hsame row endpoint)
                                                            (fun row : BHist =>
                                                              TriangulatedCatFiniteCarrier
                                                                category derived shift triangle
                                                                morphism classifier contRows
                                                                provenance endpoint probe pkg ∧
                                                                hsame row endpoint)
                                                            hsame := {
                                                        core := {
                                                          carrier_inhabited :=
                                                            Exists.intro endpoint
                                                              (And.intro carrierAgain
                                                                (hsame_refl endpoint))
                                                          equiv_refl := by
                                                            intro row _source
                                                            exact hsame_refl row
                                                          equiv_symm := by
                                                            intro _row _row' same
                                                            exact hsame_symm same
                                                          equiv_trans := by
                                                            intro _row _row' _row'' sameLeft
                                                              sameRight
                                                            exact hsame_trans sameLeft sameRight
                                                          carrier_respects_equiv := by
                                                            intro _row _row' same source
                                                            exact And.intro source.left
                                                              (hsame_trans (hsame_symm same)
                                                                source.right)
                                                        }
                                                        pattern_sound := by
                                                          intro _row source
                                                          exact source
                                                        ledger_sound := by
                                                          intro _row source
                                                          exact source
                                                      }
                                                      exact
                                                        And.intro cert
                                                          (And.intro categoryDerivedShift
                                                            (And.intro shiftTriangleMorphism
                                                              (And.intro morphismClassifierRows
                                                                (And.intro rowsProvenanceEndpoint
                                                                  pkgSig))))

inductive TriangulatedCatOctahedralLedger : List BHist -> BHist -> Prop where
  | nil {endpoint : BHist} :
      hsame endpoint BHist.Empty ->
        TriangulatedCatOctahedralLedger [] endpoint
  | face {face restEndpoint endpoint : BHist} {rest : List BHist} :
      UnaryHistory face ->
        TriangulatedCatOctahedralLedger rest restEndpoint ->
          Cont face restEndpoint endpoint ->
            TriangulatedCatOctahedralLedger (face :: rest) endpoint

theorem TriangulatedCatOctahedralLedger_boundary {rows : List BHist} {endpoint : BHist} :
    TriangulatedCatOctahedralLedger rows endpoint ->
      (forall face : BHist, List.Mem face rows -> UnaryHistory face) ∧
        (rows = [] -> hsame endpoint BHist.Empty) := by
  intro ledger
  induction ledger with
  | nil sameEndpoint =>
      constructor
      · intro face mem
        cases mem
      · intro _rowsEmpty
        exact sameEndpoint
  | face faceUnary _restLedger _contFaceRest ih =>
      constructor
      · intro row mem
        cases mem with
        | head =>
            exact faceUnary
        | tail _ tailMem =>
            exact ih.left row tailMem
      · intro rowsEmpty
        cases rowsEmpty

def TriangulatedCatPacketCarrier [AskSetup] [PackageSetup]
    (category derived additive shift triangle octahedral route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory derived ∧ UnaryHistory additive ∧
    UnaryHistory shift ∧ UnaryHistory triangle ∧ UnaryHistory octahedral ∧
      UnaryHistory route ∧ UnaryHistory endpoint ∧ Cont category derived additive ∧
        Cont shift triangle route ∧ Cont octahedral route endpoint ∧
          PkgSig bundle endpoint pkg

theorem TriangulatedCatPacketCarrier_classifier_stability [AskSetup] [PackageSetup]
    {category derived additive shift triangle octahedral route endpoint category' derived'
      additive' shift' triangle' octahedral' route' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TriangulatedCatPacketCarrier category derived additive shift triangle octahedral route
        endpoint bundle pkg ->
      hsame category category' ->
        hsame derived derived' ->
          hsame shift shift' ->
            hsame triangle triangle' ->
              hsame octahedral octahedral' ->
                Cont category' derived' additive' ->
                  Cont shift' triangle' route' ->
                    Cont octahedral' route' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        TriangulatedCatPacketCarrier category' derived' additive' shift'
                            triangle' octahedral' route' endpoint' bundle pkg ∧
                          hsame additive additive' ∧ hsame route route' ∧
                            hsame endpoint endpoint' := by
  intro carrier sameCategory sameDerived sameShift sameTriangle sameOctahedral
  intro targetAdditive targetRoute targetEndpoint targetPkg
  have sameAdditive : hsame additive additive' :=
    cont_respects_hsame sameCategory sameDerived
      carrier.right.right.right.right.right.right.right.right.left targetAdditive
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameShift sameTriangle
      carrier.right.right.right.right.right.right.right.right.right.left targetRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameOctahedral sameRoute
      carrier.right.right.right.right.right.right.right.right.right.right.left targetEndpoint
  have carrier' :
      TriangulatedCatPacketCarrier category' derived' additive' shift' triangle'
        octahedral' route' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameCategory,
      unary_transport carrier.right.left sameDerived,
      unary_transport carrier.right.right.left sameAdditive,
      unary_transport carrier.right.right.right.left sameShift,
      unary_transport carrier.right.right.right.right.left sameTriangle,
      unary_transport carrier.right.right.right.right.right.left sameOctahedral,
      unary_transport carrier.right.right.right.right.right.right.left sameRoute,
      unary_transport carrier.right.right.right.right.right.right.right.left sameEndpoint,
      targetAdditive,
      targetRoute,
      targetEndpoint,
      targetPkg⟩
  exact ⟨carrier', sameAdditive, sameRoute, sameEndpoint⟩

theorem TriangulatedCatPacketCarrier_shift_autoequivalence_obligation [AskSetup] [PackageSetup]
    {category derived additive shift triangle octahedral route endpoint shift' route'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TriangulatedCatPacketCarrier category derived additive shift triangle octahedral route
        endpoint bundle pkg ->
      hsame shift shift' ->
        Cont shift' triangle route' ->
          Cont octahedral route' endpoint' ->
            PkgSig bundle endpoint' pkg ->
              TriangulatedCatPacketCarrier category derived additive shift' triangle
                  octahedral route' endpoint' bundle pkg ∧
                hsame route route' ∧ hsame endpoint endpoint' := by
  intro carrier sameShift shiftedRoute shiftedEndpoint shiftedPkg
  have shiftUnary' : UnaryHistory shift' :=
    unary_transport carrier.right.right.right.left sameShift
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameShift (hsame_refl triangle)
      carrier.right.right.right.right.right.right.right.right.right.left shiftedRoute
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed shiftUnary' carrier.right.right.right.right.left shiftedRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl octahedral) sameRoute
      carrier.right.right.right.right.right.right.right.right.right.right.left shiftedEndpoint
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed carrier.right.right.right.right.right.left routeUnary' shiftedEndpoint
  have shiftedCarrier :
      TriangulatedCatPacketCarrier category derived additive shift' triangle octahedral route'
        endpoint' bundle pkg :=
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      shiftUnary',
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      routeUnary',
      endpointUnary',
      carrier.right.right.right.right.right.right.right.right.left,
      shiftedRoute,
      shiftedEndpoint,
      shiftedPkg⟩
  exact ⟨shiftedCarrier, sameRoute, sameEndpoint⟩

end BEDC.Derived.TriangulatedCatUp
