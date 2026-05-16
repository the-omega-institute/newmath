import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularBoundaryConditionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularBoundaryConditionUp : Type where
  | mk :
      (edgePolicy boundaryWindow updateRead admissionLedger hsameTransport contRoute
        provenance localName : BHist) →
      CellularBoundaryConditionUp
  deriving DecidableEq

def cellularBoundaryConditionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularBoundaryConditionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularBoundaryConditionEncodeBHist h

def cellularBoundaryConditionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularBoundaryConditionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularBoundaryConditionDecodeBHist tail)

private theorem cellularBoundaryConditionDecode_encode_bhist :
    ∀ h : BHist,
      cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cellularBoundaryCondition_mk_congr
    {edgePolicy edgePolicy' boundaryWindow boundaryWindow' updateRead updateRead'
      admissionLedger admissionLedger' hsameTransport hsameTransport' contRoute contRoute'
      provenance provenance' localName localName' : BHist}
    (hEdgePolicy : edgePolicy' = edgePolicy)
    (hBoundaryWindow : boundaryWindow' = boundaryWindow)
    (hUpdateRead : updateRead' = updateRead)
    (hAdmissionLedger : admissionLedger' = admissionLedger)
    (hHsameTransport : hsameTransport' = hsameTransport)
    (hContRoute : contRoute' = contRoute)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    CellularBoundaryConditionUp.mk edgePolicy' boundaryWindow' updateRead' admissionLedger'
        hsameTransport' contRoute' provenance' localName' =
      CellularBoundaryConditionUp.mk edgePolicy boundaryWindow updateRead admissionLedger
        hsameTransport contRoute provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEdgePolicy
  cases hBoundaryWindow
  cases hUpdateRead
  cases hAdmissionLedger
  cases hHsameTransport
  cases hContRoute
  cases hProvenance
  cases hLocalName
  rfl

private theorem cellularBoundaryConditionEncodeBHist_injective {h k : BHist} :
    cellularBoundaryConditionEncodeBHist h = cellularBoundaryConditionEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist h) =
        cellularBoundaryConditionDecodeBHist (cellularBoundaryConditionEncodeBHist k) :=
    congrArg cellularBoundaryConditionDecodeBHist heq
  exact Eq.trans (cellularBoundaryConditionDecode_encode_bhist h).symm
    (Eq.trans hdecode (cellularBoundaryConditionDecode_encode_bhist k))

def cellularBoundaryConditionFields : CellularBoundaryConditionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularBoundaryConditionUp.mk edgePolicy boundaryWindow updateRead admissionLedger
      hsameTransport contRoute provenance localName =>
      [edgePolicy, boundaryWindow, updateRead, admissionLedger, hsameTransport, contRoute,
        provenance, localName]

def cellularBoundaryConditionToEventFlow : CellularBoundaryConditionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularBoundaryConditionUp.mk edgePolicy boundaryWindow updateRead admissionLedger
      hsameTransport contRoute provenance localName =>
      [cellularBoundaryConditionEncodeBHist edgePolicy,
        cellularBoundaryConditionEncodeBHist boundaryWindow,
        cellularBoundaryConditionEncodeBHist updateRead,
        cellularBoundaryConditionEncodeBHist admissionLedger,
        cellularBoundaryConditionEncodeBHist hsameTransport,
        cellularBoundaryConditionEncodeBHist contRoute,
        cellularBoundaryConditionEncodeBHist provenance,
        cellularBoundaryConditionEncodeBHist localName]

def cellularBoundaryConditionFromEventFlow :
    EventFlow → Option CellularBoundaryConditionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | edgePolicy :: rest0 =>
      match rest0 with
      | [] => none
      | boundaryWindow :: rest1 =>
          match rest1 with
          | [] => none
          | updateRead :: rest2 =>
              match rest2 with
              | [] => none
              | admissionLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | hsameTransport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | contRoute :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (CellularBoundaryConditionUp.mk
                                          (cellularBoundaryConditionDecodeBHist edgePolicy)
                                          (cellularBoundaryConditionDecodeBHist boundaryWindow)
                                          (cellularBoundaryConditionDecodeBHist updateRead)
                                          (cellularBoundaryConditionDecodeBHist admissionLedger)
                                          (cellularBoundaryConditionDecodeBHist hsameTransport)
                                          (cellularBoundaryConditionDecodeBHist contRoute)
                                          (cellularBoundaryConditionDecodeBHist provenance)
                                          (cellularBoundaryConditionDecodeBHist localName))
                                  | _ :: _ => none

private theorem cellularBoundaryCondition_round_trip :
    ∀ x : CellularBoundaryConditionUp,
      cellularBoundaryConditionFromEventFlow
        (cellularBoundaryConditionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk edgePolicy boundaryWindow updateRead admissionLedger hsameTransport contRoute
      provenance localName =>
      exact
        congrArg some
          (cellularBoundaryCondition_mk_congr
            (cellularBoundaryConditionDecode_encode_bhist edgePolicy)
            (cellularBoundaryConditionDecode_encode_bhist boundaryWindow)
            (cellularBoundaryConditionDecode_encode_bhist updateRead)
            (cellularBoundaryConditionDecode_encode_bhist admissionLedger)
            (cellularBoundaryConditionDecode_encode_bhist hsameTransport)
            (cellularBoundaryConditionDecode_encode_bhist contRoute)
            (cellularBoundaryConditionDecode_encode_bhist provenance)
            (cellularBoundaryConditionDecode_encode_bhist localName))

private theorem cellularBoundaryConditionToEventFlow_injective
    {x y : CellularBoundaryConditionUp} :
    cellularBoundaryConditionToEventFlow x =
      cellularBoundaryConditionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk edgePolicy boundaryWindow updateRead admissionLedger hsameTransport contRoute
      provenance localName =>
      cases y with
      | mk edgePolicy' boundaryWindow' updateRead' admissionLedger' hsameTransport'
          contRoute' provenance' localName' =>
          injection heq with hEdgePolicy tail1
          injection tail1 with hBoundaryWindow tail2
          injection tail2 with hUpdateRead tail3
          injection tail3 with hAdmissionLedger tail4
          injection tail4 with hHsameTransport tail5
          injection tail5 with hContRoute tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hLocalName _
          exact
            cellularBoundaryCondition_mk_congr
              (cellularBoundaryConditionEncodeBHist_injective hEdgePolicy)
              (cellularBoundaryConditionEncodeBHist_injective hBoundaryWindow)
              (cellularBoundaryConditionEncodeBHist_injective hUpdateRead)
              (cellularBoundaryConditionEncodeBHist_injective hAdmissionLedger)
              (cellularBoundaryConditionEncodeBHist_injective hHsameTransport)
              (cellularBoundaryConditionEncodeBHist_injective hContRoute)
              (cellularBoundaryConditionEncodeBHist_injective hProvenance)
              (cellularBoundaryConditionEncodeBHist_injective hLocalName)

private theorem cellularBoundaryCondition_field_faithful :
    ∀ x y : CellularBoundaryConditionUp,
      cellularBoundaryConditionFields x = cellularBoundaryConditionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk edgePolicy boundaryWindow updateRead admissionLedger hsameTransport contRoute
      provenance localName =>
      cases y with
      | mk edgePolicy' boundaryWindow' updateRead' admissionLedger' hsameTransport'
          contRoute' provenance' localName' =>
          cases hfields
          rfl

instance cellularBoundaryConditionBHistCarrier :
    BHistCarrier CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularBoundaryConditionToEventFlow
  fromEventFlow := cellularBoundaryConditionFromEventFlow

instance cellularBoundaryConditionChapterTasteGate :
    ChapterTasteGate CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularBoundaryConditionFromEventFlow
        (cellularBoundaryConditionToEventFlow x) = some x
    exact cellularBoundaryCondition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularBoundaryConditionToEventFlow_injective heq)

instance cellularBoundaryConditionFieldFaithful :
    FieldFaithful CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularBoundaryConditionFields
  field_faithful := cellularBoundaryCondition_field_faithful

instance cellularBoundaryConditionNontrivial :
    Nontrivial CellularBoundaryConditionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularBoundaryConditionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularBoundaryConditionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularBoundaryConditionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularBoundaryConditionChapterTasteGate

theorem CellularBoundaryConditionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularBoundaryConditionDecodeBHist
        (cellularBoundaryConditionEncodeBHist h) = h) ∧
      (∀ x : CellularBoundaryConditionUp,
        cellularBoundaryConditionFromEventFlow
          (cellularBoundaryConditionToEventFlow x) = some x) ∧
        (∀ x y : CellularBoundaryConditionUp,
          cellularBoundaryConditionToEventFlow x =
            cellularBoundaryConditionToEventFlow y → x = y) ∧
          cellularBoundaryConditionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk edgePolicy boundaryWindow updateRead admissionLedger hsameTransport contRoute
          provenance localName =>
          exact
            congrArg some
              (cellularBoundaryCondition_mk_congr
                (cellularBoundaryConditionDecode_encode_bhist edgePolicy)
                (cellularBoundaryConditionDecode_encode_bhist boundaryWindow)
                (cellularBoundaryConditionDecode_encode_bhist updateRead)
                (cellularBoundaryConditionDecode_encode_bhist admissionLedger)
                (cellularBoundaryConditionDecode_encode_bhist hsameTransport)
                (cellularBoundaryConditionDecode_encode_bhist contRoute)
                (cellularBoundaryConditionDecode_encode_bhist provenance)
                (cellularBoundaryConditionDecode_encode_bhist localName))
    · constructor
      · intro x y heq
        exact cellularBoundaryConditionToEventFlow_injective heq
      · rfl

end BEDC.Derived.CellularBoundaryConditionUp
