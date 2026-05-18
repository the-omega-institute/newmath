import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularTrustSubstrateUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularTrustSubstrateUp : Type where
  | mk :
      (localRule orbitWindow classifier manifest auditRoute transport continuation provenance
        localName : BHist) →
        CellularTrustSubstrateUp
  deriving DecidableEq

def cellularTrustSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularTrustSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularTrustSubstrateEncodeBHist h

def cellularTrustSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularTrustSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularTrustSubstrateDecodeBHist tail)

private theorem CellularTrustSubstrateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cellularTrustSubstrateDecodeBHist
        (cellularTrustSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cellularTrustSubstrateToEventFlow :
    CellularTrustSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularTrustSubstrateUp.mk localRule orbitWindow classifier manifest auditRoute
      transport continuation provenance localName =>
      [[BMark.b0],
        cellularTrustSubstrateEncodeBHist localRule,
        [BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist orbitWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist manifest,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist auditRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularTrustSubstrateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cellularTrustSubstrateEncodeBHist localName]

def cellularTrustSubstrateFromEventFlow :
    EventFlow → Option CellularTrustSubstrateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | localRule :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | orbitWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | manifest :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | auditRoute :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (CellularTrustSubstrateUp.mk
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    localRule)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    orbitWindow)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    classifier)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    manifest)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    auditRoute)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    transport)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    continuation)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    provenance)
                                                                                  (cellularTrustSubstrateDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem CellularTrustSubstrateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CellularTrustSubstrateUp,
      cellularTrustSubstrateFromEventFlow
        (cellularTrustSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk localRule orbitWindow classifier manifest auditRoute transport continuation provenance
      localName =>
      change
        some
          (CellularTrustSubstrateUp.mk
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist localRule))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist orbitWindow))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist classifier))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist manifest))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist auditRoute))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist transport))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist continuation))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist provenance))
            (cellularTrustSubstrateDecodeBHist
              (cellularTrustSubstrateEncodeBHist localName))) =
          some
            (CellularTrustSubstrateUp.mk localRule orbitWindow classifier manifest auditRoute
              transport continuation provenance localName)
      rw [CellularTrustSubstrateTasteGate_single_carrier_alignment_decode localRule,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode orbitWindow,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode classifier,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode manifest,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode auditRoute,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode transport,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode continuation,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode provenance,
        CellularTrustSubstrateTasteGate_single_carrier_alignment_decode localName]

private theorem CellularTrustSubstrateTasteGate_single_carrier_alignment_injective
    {x y : CellularTrustSubstrateUp} :
    cellularTrustSubstrateToEventFlow x =
      cellularTrustSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularTrustSubstrateFromEventFlow (cellularTrustSubstrateToEventFlow x) =
        cellularTrustSubstrateFromEventFlow (cellularTrustSubstrateToEventFlow y) :=
    congrArg cellularTrustSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CellularTrustSubstrateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CellularTrustSubstrateTasteGate_single_carrier_alignment_round_trip y)))

instance cellularTrustSubstrateBHistCarrier :
    BHistCarrier CellularTrustSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularTrustSubstrateToEventFlow
  fromEventFlow := cellularTrustSubstrateFromEventFlow

instance cellularTrustSubstrateChapterTasteGate :
    ChapterTasteGate CellularTrustSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularTrustSubstrateFromEventFlow
        (cellularTrustSubstrateToEventFlow x) = some x
    exact CellularTrustSubstrateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CellularTrustSubstrateTasteGate_single_carrier_alignment_injective heq)

instance cellularTrustSubstrateFieldFaithful :
    FieldFaithful CellularTrustSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CellularTrustSubstrateUp.mk localRule orbitWindow classifier manifest auditRoute
        transport continuation provenance localName =>
        [localRule, orbitWindow, classifier, manifest, auditRoute, transport,
          continuation, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk localRule1 orbitWindow1 classifier1 manifest1 auditRoute1 transport1
        continuation1 provenance1 localName1 =>
        cases y with
        | mk localRule2 orbitWindow2 classifier2 manifest2 auditRoute2 transport2
            continuation2 provenance2 localName2 =>
            cases h
            rfl

instance cellularTrustSubstrateNontrivial :
    Nontrivial CellularTrustSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularTrustSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularTrustSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularTrustSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularTrustSubstrateChapterTasteGate

theorem CellularTrustSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist, cellularTrustSubstrateDecodeBHist
      (cellularTrustSubstrateEncodeBHist h) = h) ∧
      (∀ x : CellularTrustSubstrateUp, cellularTrustSubstrateFromEventFlow
        (cellularTrustSubstrateToEventFlow x) = some x) ∧
        (∀ x y : CellularTrustSubstrateUp,
          cellularTrustSubstrateToEventFlow x =
            cellularTrustSubstrateToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate CellularTrustSubstrateUp) ∧
            Nonempty (FieldFaithful CellularTrustSubstrateUp) ∧
              Nonempty (Nontrivial CellularTrustSubstrateUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CellularTrustSubstrateTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CellularTrustSubstrateTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CellularTrustSubstrateTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨cellularTrustSubstrateChapterTasteGate⟩,
            ⟨cellularTrustSubstrateFieldFaithful⟩,
            ⟨cellularTrustSubstrateNontrivial⟩⟩

theorem CellularTrustSubstrate_local_rule_window_classifier_reflect_display
    {R W K M A H C P N R' W' K' M' A' H' C' P' N' : BHist}
    (hdisplay :
      cellularTrustSubstrateToEventFlow
          (CellularTrustSubstrateUp.mk R W K M A H C P N) =
        cellularTrustSubstrateToEventFlow
          (CellularTrustSubstrateUp.mk R' W' K' M' A' H' C' P' N')) :
    R = R' ∧ W = W' ∧ K = K' ∧
      cellularTrustSubstrateEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  have hpacket :
      CellularTrustSubstrateUp.mk R W K M A H C P N =
        CellularTrustSubstrateUp.mk R' W' K' M' A' H' C' P' N' :=
    CellularTrustSubstrateTasteGate_single_carrier_alignment_injective hdisplay
  cases hpacket
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem CellularTrustSubstrate_orbit_observation_boundary
    {R W K M A H C P N R' W' K' M' A' H' C' P' N' : BHist}
    (hdisplay :
      cellularTrustSubstrateToEventFlow
          (CellularTrustSubstrateUp.mk R W K M A H C P N) =
        cellularTrustSubstrateToEventFlow
          (CellularTrustSubstrateUp.mk R' W' K' M' A' H' C' P' N')) :
    M = M' ∧ A = A' ∧
      cellularTrustSubstrateEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  have hpacket :
      CellularTrustSubstrateUp.mk R W K M A H C P N =
        CellularTrustSubstrateUp.mk R' W' K' M' A' H' C' P' N' :=
    CellularTrustSubstrateTasteGate_single_carrier_alignment_injective hdisplay
  cases hpacket
  exact ⟨rfl, rfl, rfl⟩

theorem CellularTrustSubstrate_obligation_surface
    {R W K M A H C P N : BHist}
    (ruleRoute : Cont R W K)
    (manifestRoute : Cont K M A) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row R ∧
            ∃ packet : CellularTrustSubstrateUp,
              packet = CellularTrustSubstrateUp.mk R W K M A H C P N)
        (fun row : BHist =>
          hsame row R ∧ Cont R W K ∧ Cont K M A ∧ hsame C C)
        (fun row : BHist => hsame row R ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame ∧
      cellularTrustSubstrateToEventFlow (CellularTrustSubstrateUp.mk R W K M A H C P N) =
        cellularTrustSubstrateToEventFlow (CellularTrustSubstrateUp.mk R W K M A H C P N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro R
            ⟨hsame_refl R,
              Exists.intro (CellularTrustSubstrateUp.mk R W K M A H C P N) rfl⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              source.right⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨source.left, ruleRoute, manifestRoute, hsame_refl C⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, hsame_refl H, hsame_refl P, hsame_refl N⟩
    }
  · rfl

end BEDC.Derived.CellularTrustSubstrateUp.TasteGate

namespace BEDC.Derived.CellularTrustSubstrateUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CellularTrustSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CellularTrustSubstrateUp
