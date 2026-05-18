import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverDistinctionTraceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverDistinctionTraceUp : Type where
  | mk :
      (source trace growth routes transport provenance localName : BHist) →
      ObserverDistinctionTraceUp
  deriving DecidableEq

def observerDistinctionTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerDistinctionTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerDistinctionTraceEncodeBHist h

def observerDistinctionTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerDistinctionTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerDistinctionTraceDecodeBHist tail)

private theorem observerDistinctionTrace_decode_encode_bhist :
    ∀ h : BHist,
      observerDistinctionTraceDecodeBHist (observerDistinctionTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerDistinctionTraceFields : ObserverDistinctionTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
      localName =>
      [source, trace, growth, routes, transport, provenance, localName]

def observerDistinctionTraceToEventFlow : ObserverDistinctionTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
      localName =>
      [[BMark.b0],
        observerDistinctionTraceEncodeBHist source,
        [BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist growth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerDistinctionTraceEncodeBHist localName]

def observerDistinctionTraceFromEventFlow :
    EventFlow → Option ObserverDistinctionTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | trace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | growth :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | localName :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (ObserverDistinctionTraceUp.mk
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    source)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    trace)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    growth)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    routes)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    transport)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    provenance)
                                                                  (observerDistinctionTraceDecodeBHist
                                                                    localName))
                                                          | _ :: _ => none

private theorem observerDistinctionTrace_round_trip :
    ∀ x : ObserverDistinctionTraceUp,
      observerDistinctionTraceFromEventFlow
        (observerDistinctionTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source trace growth routes transport provenance localName =>
      change
        some
          (ObserverDistinctionTraceUp.mk
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist source))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist trace))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist growth))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist routes))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist transport))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist provenance))
            (observerDistinctionTraceDecodeBHist
              (observerDistinctionTraceEncodeBHist localName))) =
          some
            (ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
              localName)
      rw [observerDistinctionTrace_decode_encode_bhist source,
        observerDistinctionTrace_decode_encode_bhist trace,
        observerDistinctionTrace_decode_encode_bhist growth,
        observerDistinctionTrace_decode_encode_bhist routes,
        observerDistinctionTrace_decode_encode_bhist transport,
        observerDistinctionTrace_decode_encode_bhist provenance,
        observerDistinctionTrace_decode_encode_bhist localName]

private theorem observerDistinctionTraceToEventFlow_injective
    {x y : ObserverDistinctionTraceUp} :
    observerDistinctionTraceToEventFlow x =
      observerDistinctionTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerDistinctionTraceFromEventFlow (observerDistinctionTraceToEventFlow x) =
        observerDistinctionTraceFromEventFlow (observerDistinctionTraceToEventFlow y) :=
    congrArg observerDistinctionTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerDistinctionTrace_round_trip x).symm
      (Eq.trans hread (observerDistinctionTrace_round_trip y)))

private theorem ObserverDistinctionTraceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ObserverDistinctionTraceUp,
      observerDistinctionTraceFields x = observerDistinctionTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source trace growth routes transport provenance localName =>
      cases y with
      | mk source' trace' growth' routes' transport' provenance' localName' =>
          cases hfields
          rfl

instance observerDistinctionTraceBHistCarrier :
    BHistCarrier ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerDistinctionTraceToEventFlow
  fromEventFlow := observerDistinctionTraceFromEventFlow

instance observerDistinctionTraceChapterTasteGate :
    ChapterTasteGate ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerDistinctionTraceFromEventFlow
        (observerDistinctionTraceToEventFlow x) = some x
    exact observerDistinctionTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerDistinctionTraceToEventFlow_injective heq)

instance observerDistinctionTraceFieldFaithful :
    FieldFaithful ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerDistinctionTraceFields
  field_faithful := ObserverDistinctionTraceTasteGate_single_carrier_alignment_field_faithful

instance observerDistinctionTraceNontrivial :
    Nontrivial ObserverDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverDistinctionTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObserverDistinctionTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverDistinctionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerDistinctionTraceChapterTasteGate

theorem ObserverDistinctionTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerDistinctionTraceDecodeBHist (observerDistinctionTraceEncodeBHist h) = h) ∧
      (∀ x : ObserverDistinctionTraceUp,
        observerDistinctionTraceFromEventFlow
          (observerDistinctionTraceToEventFlow x) = some x) ∧
        (∀ x y : ObserverDistinctionTraceUp,
          observerDistinctionTraceToEventFlow x =
            observerDistinctionTraceToEventFlow y → x = y) ∧
          observerDistinctionTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerDistinctionTrace_decode_encode_bhist
  · constructor
    · exact observerDistinctionTrace_round_trip
    · constructor
      · intro x y heq
        exact observerDistinctionTraceToEventFlow_injective heq
      · rfl

theorem ObserverDistinctionTraceNameCert_obligations
    {source trace growth routes transport provenance localName : BHist}
    (routeReplay : Cont source routes growth) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row source ∧
          ∃ packet : ObserverDistinctionTraceUp,
            packet =
              ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
                localName)
      (fun row : BHist =>
        hsame row source ∧ hsame trace trace ∧ hsame growth growth ∧ hsame routes routes)
      (fun row : BHist =>
        Cont source routes growth ∧ hsame row source ∧ hsame transport transport ∧
          hsame provenance provenance ∧ hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro source
          ⟨hsame_refl source,
            Exists.intro
              (ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
                localName)
              rfl⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, hsame_refl trace, hsame_refl growth, hsame_refl routes⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨routeReplay, sourceRow.left, hsame_refl transport, hsame_refl provenance,
          hsame_refl localName⟩
  }

theorem ObserverDistinctionTrace_temporal_factorization -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
    {source trace growth routes transport provenance localName consumer
      subjectTail : BHist}
    (routeReplay : Cont source routes growth)
    (consumerRoute : Cont growth provenance consumer) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row source ∧
            ∃ packet : ObserverDistinctionTraceUp,
              packet =
                ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
                  localName)
        (fun row : BHist =>
          hsame row source ∧ hsame trace trace ∧ hsame growth growth ∧ hsame routes routes)
        (fun row : BHist =>
          Cont source routes growth ∧ hsame row source ∧ hsame transport transport ∧
            hsame provenance provenance ∧ hsame localName localName)
        hsame ∧
      Cont growth provenance consumer ∧
        (Cont consumer (BHist.e0 subjectTail) growth → False) ∧
          (Cont consumer (BHist.e1 subjectTail) growth → False) := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  exact
    ⟨ObserverDistinctionTraceNameCert_obligations
        (source := source) (trace := trace) (growth := growth) (routes := routes)
        (transport := transport) (provenance := provenance) (localName := localName)
        routeReplay,
      consumerRoute,
      (fun subjectReturn =>
        cont_mutual_extension_right_tail_absurd.left consumerRoute subjectReturn),
      (fun subjectReturn =>
        cont_mutual_extension_right_tail_absurd.right consumerRoute subjectReturn)⟩

theorem ObserverDistinctionTrace_nonescape
    {source trace growth routes transport provenance localName consumer subjectTail : BHist}
    (routeReplay : Cont source routes growth)
    (consumerRoute : Cont growth provenance consumer) :
    (∃ packet : ObserverDistinctionTraceUp,
        packet =
          ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
            localName) ∧
      Cont growth provenance consumer ∧
        (Cont consumer (BHist.e0 subjectTail) growth → False) ∧
          (Cont consumer (BHist.e1 subjectTail) growth → False) := by
  -- BEDC touchpoint anchor: BHist Cont
  have _cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row source ∧
            ∃ packet : ObserverDistinctionTraceUp,
              packet =
                ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
                  localName)
        (fun row : BHist =>
          hsame row source ∧ hsame trace trace ∧ hsame growth growth ∧ hsame routes routes)
        (fun row : BHist =>
          Cont source routes growth ∧ hsame row source ∧ hsame transport transport ∧
            hsame provenance provenance ∧ hsame localName localName)
        hsame :=
    ObserverDistinctionTraceNameCert_obligations
      (source := source) (trace := trace) (growth := growth) (routes := routes)
      (transport := transport) (provenance := provenance) (localName := localName)
      routeReplay
  exact
    ⟨⟨ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
          localName,
        rfl⟩,
      consumerRoute,
      (fun subjectReturn =>
        cont_mutual_extension_right_tail_absurd.left consumerRoute subjectReturn),
      (fun subjectReturn =>
        cont_mutual_extension_right_tail_absurd.right consumerRoute subjectReturn)⟩

theorem ObserverDistinctionTrace_public_route
    {source trace growth routes transport provenance localName consumer
      subjectTail : BHist}
    (routeReplay : Cont source routes growth)
    (consumerRoute : Cont growth provenance consumer)
    (clockRoute : Cont BHist.Empty trace source)
    (localBudgetRoute : Cont trace routes transport) :
    (SemanticNameCert
        (fun row : BHist =>
          hsame row source ∧
            ∃ packet : ObserverDistinctionTraceUp,
              packet =
                ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
                  localName)
        (fun row : BHist =>
          hsame row source ∧ hsame trace trace ∧ hsame growth growth ∧ hsame routes routes)
        (fun row : BHist =>
          Cont source routes growth ∧ hsame row source ∧ hsame transport transport ∧
            hsame provenance provenance ∧ hsame localName localName)
        hsame ∧
      Cont growth provenance consumer ∧
        (Cont consumer (BHist.e0 subjectTail) growth → False) ∧
          (Cont consumer (BHist.e1 subjectTail) growth → False)) ∧
      Cont BHist.Empty trace source ∧
        Cont trace routes transport ∧
          observerDistinctionTraceFields
            (ObserverDistinctionTraceUp.mk source trace growth routes transport provenance
              localName) =
            [source, trace, growth, routes, transport, provenance, localName] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  exact
    ⟨@ObserverDistinctionTrace_temporal_factorization source trace growth routes transport
        provenance localName consumer subjectTail routeReplay consumerRoute,
      clockRoute, localBudgetRoute, rfl⟩

end BEDC.Derived.ObserverDistinctionTraceUp
