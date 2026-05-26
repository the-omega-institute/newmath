import BEDC.Derived.LocalTimeFiberUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalTimeFiberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def localTimeFiberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localTimeFiberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localTimeFiberEncodeBHist h

def localTimeFiberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localTimeFiberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localTimeFiberDecodeBHist tail)

private theorem localTimeFiberDecode_encode_bhist :
    ∀ h : BHist, localTimeFiberDecodeBHist (localTimeFiberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def localTimeFiberFields : BEDC.Derived.LocalTimeFiberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.LocalTimeFiberUp.mk observerSource localStream localClockBudget
      synchronizationBoundary refusal transport replay provenance name =>
      [observerSource, localStream, localClockBudget, synchronizationBoundary, refusal,
        transport, replay, provenance, name]

def localTimeFiberToEventFlow : BEDC.Derived.LocalTimeFiberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.LocalTimeFiberUp.mk observerSource localStream localClockBudget
      synchronizationBoundary refusal transport replay provenance name =>
      [[BMark.b1, BMark.b0, BMark.b0, BMark.b1],
        localTimeFiberEncodeBHist observerSource,
        localTimeFiberEncodeBHist localStream,
        localTimeFiberEncodeBHist localClockBudget,
        localTimeFiberEncodeBHist synchronizationBoundary,
        localTimeFiberEncodeBHist refusal,
        localTimeFiberEncodeBHist transport,
        localTimeFiberEncodeBHist replay,
        localTimeFiberEncodeBHist provenance,
        localTimeFiberEncodeBHist name]

def localTimeFiberFromEventFlow : EventFlow → Option BEDC.Derived.LocalTimeFiberUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | observerSource :: rest1 =>
          match rest1 with
          | [] => none
          | localStream :: rest2 =>
              match rest2 with
              | [] => none
              | localClockBudget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | synchronizationBoundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (BEDC.Derived.LocalTimeFiberUp.mk
                                                  (localTimeFiberDecodeBHist observerSource)
                                                  (localTimeFiberDecodeBHist localStream)
                                                  (localTimeFiberDecodeBHist localClockBudget)
                                                  (localTimeFiberDecodeBHist
                                                    synchronizationBoundary)
                                                  (localTimeFiberDecodeBHist refusal)
                                                  (localTimeFiberDecodeBHist transport)
                                                  (localTimeFiberDecodeBHist replay)
                                                  (localTimeFiberDecodeBHist provenance)
                                                  (localTimeFiberDecodeBHist name))
                                          | _ :: _ => none

private theorem localTimeFiber_round_trip :
    ∀ x : BEDC.Derived.LocalTimeFiberUp,
      localTimeFiberFromEventFlow (localTimeFiberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerSource localStream localClockBudget synchronizationBoundary refusal transport
      replay provenance name =>
      change
        some
          (BEDC.Derived.LocalTimeFiberUp.mk
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist observerSource))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist localStream))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist localClockBudget))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist synchronizationBoundary))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist refusal))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist transport))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist replay))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist provenance))
            (localTimeFiberDecodeBHist (localTimeFiberEncodeBHist name))) =
          some
            (BEDC.Derived.LocalTimeFiberUp.mk observerSource localStream localClockBudget
              synchronizationBoundary refusal transport replay provenance name)
      rw [localTimeFiberDecode_encode_bhist observerSource,
        localTimeFiberDecode_encode_bhist localStream,
        localTimeFiberDecode_encode_bhist localClockBudget,
        localTimeFiberDecode_encode_bhist synchronizationBoundary,
        localTimeFiberDecode_encode_bhist refusal,
        localTimeFiberDecode_encode_bhist transport,
        localTimeFiberDecode_encode_bhist replay,
        localTimeFiberDecode_encode_bhist provenance,
        localTimeFiberDecode_encode_bhist name]

private theorem localTimeFiberToEventFlow_injective
    {x y : BEDC.Derived.LocalTimeFiberUp} :
    localTimeFiberToEventFlow x = localTimeFiberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localTimeFiberFromEventFlow (localTimeFiberToEventFlow x) =
        localTimeFiberFromEventFlow (localTimeFiberToEventFlow y) :=
    congrArg localTimeFiberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localTimeFiber_round_trip x).symm
      (Eq.trans hread (localTimeFiber_round_trip y)))

private theorem localTimeFiber_fields_faithful :
    ∀ x y : BEDC.Derived.LocalTimeFiberUp,
      localTimeFiberFields x = localTimeFiberFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observerSource1 localStream1 localClockBudget1 synchronizationBoundary1 refusal1
      transport1 replay1 provenance1 name1 =>
      cases y with
      | mk observerSource2 localStream2 localClockBudget2 synchronizationBoundary2 refusal2
          transport2 replay2 provenance2 name2 =>
          cases hfields
          rfl

instance localTimeFiberBHistCarrier : BHistCarrier BEDC.Derived.LocalTimeFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localTimeFiberToEventFlow
  fromEventFlow := localTimeFiberFromEventFlow

instance localTimeFiberChapterTasteGate :
    ChapterTasteGate BEDC.Derived.LocalTimeFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change localTimeFiberFromEventFlow (localTimeFiberToEventFlow x) = some x
    exact localTimeFiber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localTimeFiberToEventFlow_injective heq)

instance localTimeFiberFieldFaithful :
    FieldFaithful BEDC.Derived.LocalTimeFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := localTimeFiberFields
  field_faithful := localTimeFiber_fields_faithful

instance localTimeFiberNontrivial : Nontrivial BEDC.Derived.LocalTimeFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.LocalTimeFiberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BEDC.Derived.LocalTimeFiberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.LocalTimeFiberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  localTimeFiberChapterTasteGate

namespace TasteGate

theorem LocalTimeFiberTasteGate_single_carrier_alignment :
    (forall h : BHist, localTimeFiberDecodeBHist (localTimeFiberEncodeBHist h) = h) ∧
      (forall x : BEDC.Derived.LocalTimeFiberUp,
        localTimeFiberFromEventFlow (localTimeFiberToEventFlow x) = some x) ∧
        (forall x y : BEDC.Derived.LocalTimeFiberUp,
          localTimeFiberToEventFlow x = localTimeFiberToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨localTimeFiberDecode_encode_bhist, localTimeFiber_round_trip,
      fun _ _ heq => localTimeFiberToEventFlow_injective heq⟩

end TasteGate

end BEDC.Derived.LocalTimeFiberUp
