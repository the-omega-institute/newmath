import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticResidueLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticResidueLedgerUp : Type where
  | mk :
      (ontic modelAudit modelState access classifier residue transport route provenance
        nameCert : BHist) →
      OnticResidueLedgerUp
  deriving DecidableEq

def onticResidueLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticResidueLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticResidueLedgerEncodeBHist h

def onticResidueLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticResidueLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticResidueLedgerDecodeBHist tail)

private theorem onticResidueLedgerDecode_encode_bhist :
    ∀ h : BHist, onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def onticResidueLedgerFields : OnticResidueLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticResidueLedgerUp.mk ontic modelAudit modelState access classifier residue transport
      route provenance nameCert =>
      [ontic, modelAudit, modelState, access, classifier, residue, transport, route,
        provenance, nameCert]

def onticResidueLedgerToEventFlow : OnticResidueLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OnticResidueLedgerUp.mk ontic modelAudit modelState access classifier residue transport
      route provenance nameCert =>
      [onticResidueLedgerEncodeBHist ontic,
        onticResidueLedgerEncodeBHist modelAudit,
        onticResidueLedgerEncodeBHist modelState,
        onticResidueLedgerEncodeBHist access,
        onticResidueLedgerEncodeBHist classifier,
        onticResidueLedgerEncodeBHist residue,
        onticResidueLedgerEncodeBHist transport,
        onticResidueLedgerEncodeBHist route,
        onticResidueLedgerEncodeBHist provenance,
        onticResidueLedgerEncodeBHist nameCert]

def onticResidueLedgerFromEventFlow : EventFlow → Option OnticResidueLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | ontic :: rest0 =>
      match rest0 with
      | [] => none
      | modelAudit :: rest1 =>
          match rest1 with
          | [] => none
          | modelState :: rest2 =>
              match rest2 with
              | [] => none
              | access :: rest3 =>
                  match rest3 with
                  | [] => none
                  | classifier :: rest4 =>
                      match rest4 with
                      | [] => none
                      | residue :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (OnticResidueLedgerUp.mk
                                                  (onticResidueLedgerDecodeBHist ontic)
                                                  (onticResidueLedgerDecodeBHist modelAudit)
                                                  (onticResidueLedgerDecodeBHist modelState)
                                                  (onticResidueLedgerDecodeBHist access)
                                                  (onticResidueLedgerDecodeBHist classifier)
                                                  (onticResidueLedgerDecodeBHist residue)
                                                  (onticResidueLedgerDecodeBHist transport)
                                                  (onticResidueLedgerDecodeBHist route)
                                                  (onticResidueLedgerDecodeBHist provenance)
                                                  (onticResidueLedgerDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem onticResidueLedger_round_trip :
    ∀ x : OnticResidueLedgerUp,
      onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ontic modelAudit modelState access classifier residue transport route provenance
      nameCert =>
      change
        some
          (OnticResidueLedgerUp.mk
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist ontic))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist modelAudit))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist modelState))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist access))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist classifier))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist residue))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist transport))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist route))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist provenance))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist nameCert))) =
          some
            (OnticResidueLedgerUp.mk ontic modelAudit modelState access classifier residue
              transport route provenance nameCert)
      rw [onticResidueLedgerDecode_encode_bhist ontic,
        onticResidueLedgerDecode_encode_bhist modelAudit,
        onticResidueLedgerDecode_encode_bhist modelState,
        onticResidueLedgerDecode_encode_bhist access,
        onticResidueLedgerDecode_encode_bhist classifier,
        onticResidueLedgerDecode_encode_bhist residue,
        onticResidueLedgerDecode_encode_bhist transport,
        onticResidueLedgerDecode_encode_bhist route,
        onticResidueLedgerDecode_encode_bhist provenance,
        onticResidueLedgerDecode_encode_bhist nameCert]

private theorem onticResidueLedgerToEventFlow_injective {x y : OnticResidueLedgerUp} :
    onticResidueLedgerToEventFlow x = onticResidueLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) =
        onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow y) :=
    congrArg onticResidueLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticResidueLedger_round_trip x).symm
      (Eq.trans hread (onticResidueLedger_round_trip y)))

private theorem OnticResidueLedgerTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : OnticResidueLedgerUp,
      onticResidueLedgerFields x = onticResidueLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk ontic modelAudit modelState access classifier residue transport route provenance
      nameCert =>
      cases y with
      | mk ontic' modelAudit' modelState' access' classifier' residue' transport' route'
          provenance' nameCert' =>
          injection hfields with hOntic hTail0
          injection hTail0 with hModelAudit hTail1
          injection hTail1 with hModelState hTail2
          injection hTail2 with hAccess hTail3
          injection hTail3 with hClassifier hTail4
          injection hTail4 with hResidue hTail5
          injection hTail5 with hTransport hTail6
          injection hTail6 with hRoute hTail7
          injection hTail7 with hProvenance hTail8
          injection hTail8 with hNameCert _hNil
          cases hOntic
          cases hModelAudit
          cases hModelState
          cases hAccess
          cases hClassifier
          cases hResidue
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hNameCert
          rfl

instance onticResidueLedgerBHistCarrier : BHistCarrier OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticResidueLedgerToEventFlow
  fromEventFlow := onticResidueLedgerFromEventFlow

instance onticResidueLedgerChapterTasteGate : ChapterTasteGate OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) = some x
    exact onticResidueLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticResidueLedgerToEventFlow_injective heq)

instance onticResidueLedgerFieldFaithful : FieldFaithful OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := onticResidueLedgerFields
  field_faithful := OnticResidueLedgerTasteGate_single_carrier_alignment_field_faithful

instance onticResidueLedgerNontrivial : Nontrivial OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OnticResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onticResidueLedgerChapterTasteGate

theorem OnticResidueLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist h) = h) ∧
      (∀ x : OnticResidueLedgerUp,
        onticResidueLedgerToEventFlow x =
          List.map onticResidueLedgerEncodeBHist (onticResidueLedgerFields x)) ∧
        (∀ x y : OnticResidueLedgerUp,
          onticResidueLedgerFields x = onticResidueLedgerFields y → x = y) ∧
          (∃ x y : OnticResidueLedgerUp, x ≠ y) ∧
            onticResidueLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
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
      | mk ontic modelAudit modelState access classifier residue transport route provenance
          nameCert =>
          rfl
    · constructor
      · intro x y hfields
        cases x with
        | mk ontic modelAudit modelState access classifier residue transport route provenance
            nameCert =>
            cases y with
            | mk ontic2 modelAudit2 modelState2 access2 classifier2 residue2 transport2 route2
                provenance2 nameCert2 =>
                injection hfields with hOntic hTail0
                injection hTail0 with hModelAudit hTail1
                injection hTail1 with hModelState hTail2
                injection hTail2 with hAccess hTail3
                injection hTail3 with hClassifier hTail4
                injection hTail4 with hResidue hTail5
                injection hTail5 with hTransport hTail6
                injection hTail6 with hRoute hTail7
                injection hTail7 with hProvenance hTail8
                injection hTail8 with hNameCert _hNil
                cases hOntic
                cases hModelAudit
                cases hModelState
                cases hAccess
                cases hClassifier
                cases hResidue
                cases hTransport
                cases hRoute
                cases hProvenance
                cases hNameCert
                rfl
      · constructor
        · exact
            ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end BEDC.Derived.OnticResidueLedgerUp.TasteGate

namespace BEDC.Derived.OnticResidueLedgerUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.OnticResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.OnticResidueLedgerUp
