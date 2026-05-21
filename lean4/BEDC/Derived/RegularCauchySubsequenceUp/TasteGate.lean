import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceUp : Type where
  | packet
      (source reindex windows radius «seal» sameRows routeRows provenance localCert
        endpoint : BHist)
      (sourceReindexWindows : Cont source reindex windows)
      (windowsRadiusSeal : Cont windows radius «seal»)
      (sameRowsRouteRowsProvenance : Cont sameRows routeRows provenance)
      (provenanceLocalCertEndpoint : Cont provenance localCert endpoint)
      (endpointReadback : hsame endpoint (append provenance localCert)) :
      RegularCauchySubsequenceUp

def regularCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceEncodeBHist h

def regularCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceDecodeBHist tail)

private theorem regularCauchySubsequenceDecode_encode :
    ∀ h : BHist,
      regularCauchySubsequenceDecodeBHist (regularCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchySubsequenceFields : RegularCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubsequenceUp.packet source reindex windows radius «seal» sameRows routeRows
      provenance localCert endpoint _ _ _ _ _ =>
      [source, reindex, windows, radius, «seal», sameRows, routeRows, provenance,
        localCert, endpoint]

def regularCauchySubsequenceToEventFlow : RegularCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySubsequenceFields x).map regularCauchySubsequenceEncodeBHist

def regularCauchySubsequenceFromEventFlow : EventFlow → Option RegularCauchySubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | source :: reindex :: windows :: radius :: «seal» :: sameRows :: routeRows ::
      provenance :: localCert :: endpoint :: [] =>
      let source := regularCauchySubsequenceDecodeBHist source
      let reindex := regularCauchySubsequenceDecodeBHist reindex
      let windows := regularCauchySubsequenceDecodeBHist windows
      let radius := regularCauchySubsequenceDecodeBHist radius
      let «seal» := regularCauchySubsequenceDecodeBHist «seal»
      let sameRows := regularCauchySubsequenceDecodeBHist sameRows
      let routeRows := regularCauchySubsequenceDecodeBHist routeRows
      let provenance := regularCauchySubsequenceDecodeBHist provenance
      let localCert := regularCauchySubsequenceDecodeBHist localCert
      let endpoint := regularCauchySubsequenceDecodeBHist endpoint
      if sourceReindexWindows : windows = append source reindex then
        if windowsRadiusSeal : «seal» = append windows radius then
          if sameRowsRouteRowsProvenance : provenance = append sameRows routeRows then
            if provenanceLocalCertEndpoint : endpoint = append provenance localCert then
              if endpointReadback : endpoint = append provenance localCert then
                some
                  (RegularCauchySubsequenceUp.packet source reindex windows radius «seal»
                    sameRows routeRows provenance localCert endpoint sourceReindexWindows
                    windowsRadiusSeal sameRowsRouteRowsProvenance provenanceLocalCertEndpoint
                    endpointReadback)
              else
                none
            else
              none
          else
            none
        else
          none
      else
        none
  | _ => none

private theorem regularCauchySubsequence_round_trip :
    ∀ x : RegularCauchySubsequenceUp,
      regularCauchySubsequenceFromEventFlow (regularCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro x
  cases x with
  | packet source reindex windows radius sealRow sameRows routeRows provenance localCert endpoint
      sourceReindexWindows windowsRadiusSeal sameRowsRouteRowsProvenance
      provenanceLocalCertEndpoint endpointReadback =>
      dsimp [regularCauchySubsequenceToEventFlow, regularCauchySubsequenceFields,
        regularCauchySubsequenceFromEventFlow]
      change windows = append source reindex at sourceReindexWindows
      change sealRow = append windows radius at windowsRadiusSeal
      change provenance = append sameRows routeRows at sameRowsRouteRowsProvenance
      change endpoint = append provenance localCert at provenanceLocalCertEndpoint
      change endpoint = append provenance localCert at endpointReadback
      simp only [regularCauchySubsequenceDecode_encode, sourceReindexWindows,
        windowsRadiusSeal, sameRowsRouteRowsProvenance, provenanceLocalCertEndpoint,
        dite_true]

private theorem regularCauchySubsequenceToEventFlow_injective
    {x y : RegularCauchySubsequenceUp} :
    regularCauchySubsequenceToEventFlow x = regularCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubsequenceFromEventFlow (regularCauchySubsequenceToEventFlow x) =
        regularCauchySubsequenceFromEventFlow (regularCauchySubsequenceToEventFlow y) :=
    congrArg regularCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubsequence_round_trip x).symm
      (Eq.trans hread (regularCauchySubsequence_round_trip y)))

private theorem regularCauchySubsequenceFields_faithful :
    ∀ x y : RegularCauchySubsequenceUp,
      regularCauchySubsequenceFields x = regularCauchySubsequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro x y h
  cases x with
  | packet source₁ reindex₁ windows₁ radius₁ seal₁ sameRows₁ routeRows₁ provenance₁
      localCert₁ endpoint₁ sourceReindexWindows₁ windowsRadiusSeal₁
      sameRowsRouteRowsProvenance₁ provenanceLocalCertEndpoint₁ endpointReadback₁ =>
      cases y with
      | packet source₂ reindex₂ windows₂ radius₂ seal₂ sameRows₂ routeRows₂ provenance₂
          localCert₂ endpoint₂ sourceReindexWindows₂ windowsRadiusSeal₂
          sameRowsRouteRowsProvenance₂ provenanceLocalCertEndpoint₂ endpointReadback₂ =>
          injection h with hSource t1
          injection t1 with hReindex t2
          injection t2 with hWindows t3
          injection t3 with hRadius t4
          injection t4 with hSeal t5
          injection t5 with hSameRows t6
          injection t6 with hRouteRows t7
          injection t7 with hProvenance t8
          injection t8 with hLocalCert t9
          injection t9 with hEndpoint _
          subst hSource
          subst hReindex
          subst hWindows
          subst hRadius
          subst hSeal
          subst hSameRows
          subst hRouteRows
          subst hProvenance
          subst hLocalCert
          subst hEndpoint
          rfl

instance regularCauchySubsequenceBHistCarrier : BHistCarrier RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceToEventFlow
  fromEventFlow := regularCauchySubsequenceFromEventFlow

instance regularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceFromEventFlow (regularCauchySubsequenceToEventFlow x) =
        some x
    exact regularCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubsequenceToEventFlow_injective heq)

instance regularCauchySubsequenceFieldFaithful :
    FieldFaithful RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySubsequenceFields
  field_faithful := regularCauchySubsequenceFields_faithful

instance regularCauchySubsequenceNontrivial : Nontrivial RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  witness_pair :=
    ⟨RegularCauchySubsequenceUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty rfl rfl rfl rfl
        rfl,
      RegularCauchySubsequenceUp.packet BHist.Empty (BHist.e0 BHist.Empty)
        (BHist.e0 BHist.Empty) BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty rfl rfl rfl rfl rfl,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubsequenceChapterTasteGate

end BEDC.Derived.RegularCauchySubsequenceUp.TasteGate
