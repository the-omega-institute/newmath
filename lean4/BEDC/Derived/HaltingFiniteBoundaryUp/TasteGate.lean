import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingFiniteBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingFiniteBoundaryUp : Type where
  | mk :
      (admitted finiteTrace consumer refusal terminalTrace inscription transport route
        provenance name : BHist) →
      HaltingFiniteBoundaryUp
  deriving DecidableEq

def haltingFiniteBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingFiniteBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingFiniteBoundaryEncodeBHist h

def haltingFiniteBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingFiniteBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingFiniteBoundaryDecodeBHist tail)

private theorem haltingFiniteBoundaryDecode_encode_bhist :
    ∀ h : BHist, haltingFiniteBoundaryDecodeBHist (haltingFiniteBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem haltingFiniteBoundary_mk_congr
    {admitted admitted' finiteTrace finiteTrace' consumer consumer' refusal refusal'
      terminalTrace terminalTrace' inscription inscription' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hAdmitted : admitted' = admitted)
    (hFiniteTrace : finiteTrace' = finiteTrace)
    (hConsumer : consumer' = consumer)
    (hRefusal : refusal' = refusal)
    (hTerminalTrace : terminalTrace' = terminalTrace)
    (hInscription : inscription' = inscription)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    HaltingFiniteBoundaryUp.mk admitted' finiteTrace' consumer' refusal' terminalTrace'
        inscription' transport' route' provenance' name' =
      HaltingFiniteBoundaryUp.mk admitted finiteTrace consumer refusal terminalTrace inscription
        transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAdmitted
  cases hFiniteTrace
  cases hConsumer
  cases hRefusal
  cases hTerminalTrace
  cases hInscription
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def haltingFiniteBoundaryFields : HaltingFiniteBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingFiniteBoundaryUp.mk admitted finiteTrace consumer refusal terminalTrace inscription
      transport route provenance name =>
      [admitted, finiteTrace, consumer, refusal, terminalTrace, inscription, transport, route,
        provenance, name]

def haltingFiniteBoundaryToEventFlow : HaltingFiniteBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingFiniteBoundaryUp.mk admitted finiteTrace consumer refusal terminalTrace inscription
      transport route provenance name =>
      [haltingFiniteBoundaryEncodeBHist admitted,
        haltingFiniteBoundaryEncodeBHist finiteTrace,
        haltingFiniteBoundaryEncodeBHist consumer,
        haltingFiniteBoundaryEncodeBHist refusal,
        haltingFiniteBoundaryEncodeBHist terminalTrace,
        haltingFiniteBoundaryEncodeBHist inscription,
        haltingFiniteBoundaryEncodeBHist transport,
        haltingFiniteBoundaryEncodeBHist route,
        haltingFiniteBoundaryEncodeBHist provenance,
        haltingFiniteBoundaryEncodeBHist name]

def haltingFiniteBoundaryFromEventFlow : EventFlow → Option HaltingFiniteBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [admitted, finiteTrace, consumer, refusal, terminalTrace, inscription, transport, route,
      provenance, name] =>
      some
        (HaltingFiniteBoundaryUp.mk
          (haltingFiniteBoundaryDecodeBHist admitted)
          (haltingFiniteBoundaryDecodeBHist finiteTrace)
          (haltingFiniteBoundaryDecodeBHist consumer)
          (haltingFiniteBoundaryDecodeBHist refusal)
          (haltingFiniteBoundaryDecodeBHist terminalTrace)
          (haltingFiniteBoundaryDecodeBHist inscription)
          (haltingFiniteBoundaryDecodeBHist transport)
          (haltingFiniteBoundaryDecodeBHist route)
          (haltingFiniteBoundaryDecodeBHist provenance)
          (haltingFiniteBoundaryDecodeBHist name))
  | _ => none

private theorem haltingFiniteBoundary_round_trip :
    ∀ x : HaltingFiniteBoundaryUp,
      haltingFiniteBoundaryFromEventFlow (haltingFiniteBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk admitted finiteTrace consumer refusal terminalTrace inscription transport route
      provenance name =>
      exact
        congrArg some
          (haltingFiniteBoundary_mk_congr
            (haltingFiniteBoundaryDecode_encode_bhist admitted)
            (haltingFiniteBoundaryDecode_encode_bhist finiteTrace)
            (haltingFiniteBoundaryDecode_encode_bhist consumer)
            (haltingFiniteBoundaryDecode_encode_bhist refusal)
            (haltingFiniteBoundaryDecode_encode_bhist terminalTrace)
            (haltingFiniteBoundaryDecode_encode_bhist inscription)
            (haltingFiniteBoundaryDecode_encode_bhist transport)
            (haltingFiniteBoundaryDecode_encode_bhist route)
            (haltingFiniteBoundaryDecode_encode_bhist provenance)
            (haltingFiniteBoundaryDecode_encode_bhist name))

private theorem haltingFiniteBoundaryToEventFlow_injective {x y : HaltingFiniteBoundaryUp} :
    haltingFiniteBoundaryToEventFlow x = haltingFiniteBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingFiniteBoundaryFromEventFlow (haltingFiniteBoundaryToEventFlow x) =
        haltingFiniteBoundaryFromEventFlow (haltingFiniteBoundaryToEventFlow y) :=
    congrArg haltingFiniteBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingFiniteBoundary_round_trip x).symm
      (Eq.trans hread (haltingFiniteBoundary_round_trip y)))

theorem HaltingFiniteBoundaryTasteGate_field_faithful_concrete :
    ∀ x y : HaltingFiniteBoundaryUp, haltingFiniteBoundaryFields x = haltingFiniteBoundaryFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk admitted finiteTrace consumer refusal terminalTrace inscription transport route
      provenance name =>
      cases y with
      | mk admitted' finiteTrace' consumer' refusal' terminalTrace' inscription' transport'
          route' provenance' name' =>
          cases hfields
          rfl

instance haltingFiniteBoundaryBHistCarrier : BHistCarrier HaltingFiniteBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingFiniteBoundaryToEventFlow
  fromEventFlow := haltingFiniteBoundaryFromEventFlow

instance haltingFiniteBoundaryChapterTasteGate :
    ChapterTasteGate HaltingFiniteBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haltingFiniteBoundaryFromEventFlow (haltingFiniteBoundaryToEventFlow x) = some x
    exact haltingFiniteBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingFiniteBoundaryToEventFlow_injective heq)

instance haltingFiniteBoundaryFieldFaithful :
    FieldFaithful HaltingFiniteBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := haltingFiniteBoundaryFields
  field_faithful := HaltingFiniteBoundaryTasteGate_field_faithful_concrete

instance haltingFiniteBoundaryNontrivial : Nontrivial HaltingFiniteBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HaltingFiniteBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HaltingFiniteBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HaltingFiniteBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haltingFiniteBoundaryChapterTasteGate

theorem HaltingFiniteBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, haltingFiniteBoundaryDecodeBHist (haltingFiniteBoundaryEncodeBHist h) = h) ∧
      haltingFiniteBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : HaltingFiniteBoundaryUp,
          haltingFiniteBoundaryFields x = haltingFiniteBoundaryFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact haltingFiniteBoundaryDecode_encode_bhist
  · constructor
    · rfl
    · exact HaltingFiniteBoundaryTasteGate_field_faithful_concrete

theorem HaltingFiniteBoundaryCarrier_consumer_inversion (x : HaltingFiniteBoundaryUp) :
    ∃ A F R D T I H C P N : BHist,
      x = HaltingFiniteBoundaryUp.mk A F R D T I H C P N ∧
        Cont F D (append F D) ∧
          hsame R R ∧
            haltingFiniteBoundaryFields x = [A, F, R, D, T, I, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases x with
  | mk A F R D T I H C P N =>
      exact ⟨A, F, R, D, T, I, H, C, P, N, rfl, rfl, hsame_refl R, rfl⟩

end BEDC.Derived.HaltingFiniteBoundaryUp
