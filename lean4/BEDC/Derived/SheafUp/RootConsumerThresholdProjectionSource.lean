import BEDC.Derived.SheafUp
import BEDC.Derived.SheafUp.DownstreamProjection

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootConsumerThresholdProjectionSource
    (_point _openHist sectionA sectionB _germA _germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist) : Prop :=
  SheafRootFaceRead restrictedOpen restrictedGermA SheafRootFaceLanding.restrictionRoute ∧
    SheafRootFaceRead restrictedOpen restrictedGermB SheafRootFaceLanding.restrictionRoute ∧
      Cont restrictedOpen sectionA restrictedGermA ∧
        Cont restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB ∧ hsame chartEndpoint restrictedGermB

theorem SheafRootConsumerThresholdProjectionSource_projection_faces
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafRootConsumerThresholdProjectionSource point openHist sectionA sectionB germA germB
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint := by
  intro scope
  have projectionRows :=
    SheafRootConsumerRingedSpaceProjection_semantic_name_certificate
      (point := point) (openHist := openHist) (sectionA := sectionA) (sectionB := sectionB)
      (germA := germA) (germB := germB) (restrictedOpen := restrictedOpen)
      (restrictedGermA := restrictedGermA) (restrictedGermB := restrictedGermB)
      (chartEndpoint := chartEndpoint) scope
  have boundaryRows :=
    SheafDownstreamConsumer_RingedSpace_boundary_rows
      (point := point) (openHist := openHist) (sectionA := sectionA) (sectionB := sectionB)
      (germA := germA) (germB := germB) (restrictedOpen := restrictedOpen)
      (restrictedGermA := restrictedGermA) (restrictedGermB := restrictedGermB)
      (chartEndpoint := chartEndpoint) scope
  exact And.intro projectionRows.right.left
    (And.intro projectionRows.right.right.left
      (And.intro boundaryRows.right.right.right.left
        (And.intro boundaryRows.right.right.right.right
          (And.intro projectionRows.right.right.right boundaryRows.right.left))))

def SheafRootConsumerThresholdProjection_source
    (root ringed scheme pullback ledger : BHist) : Prop :=
  SheafConsumerAccessTrace root [ringed, scheme, pullback] ∧ UnaryHistory ledger ∧
    Cont root ledger pullback

theorem SheafRootConsumerThresholdProjection_source_rows
    {root ringed scheme pullback ledger : BHist} :
    SheafRootConsumerThresholdProjection_source root ringed scheme pullback ledger ->
      UnaryHistory root ∧ UnaryHistory ringed ∧ UnaryHistory scheme ∧
        UnaryHistory pullback ∧ UnaryHistory ledger ∧ Cont root ledger pullback := by
  intro source
  have ringedRow : UnaryHistory ringed :=
    source.left.right ringed (List.Mem.head [scheme, pullback])
  have schemeRow : UnaryHistory scheme :=
    source.left.right scheme (List.Mem.tail ringed (List.Mem.head [pullback]))
  have pullbackRow : UnaryHistory pullback :=
    source.left.right pullback
      (List.Mem.tail ringed (List.Mem.tail scheme (List.Mem.head [])))
  exact And.intro source.left.left
    (And.intro ringedRow
      (And.intro schemeRow
        (And.intro pullbackRow
          (And.intro source.right.left source.right.right))))

end BEDC.Derived.SheafUp
