import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannSumConsistencyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannSumConsistencyUp : Type where
  | mk (riemannSum darbouxEnvelope finiteMesh regulatedFunction realSeal transport replay
      provenance localName : BHist) : RiemannSumConsistencyUp
  deriving DecidableEq

def riemannSumConsistencyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannSumConsistencyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannSumConsistencyEncodeBHist h

def riemannSumConsistencyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannSumConsistencyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannSumConsistencyDecodeBHist tail)

private theorem RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RiemannSumConsistencyTasteGate_single_carrier_alignment_fields :
    RiemannSumConsistencyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannSumConsistencyUp.mk riemannSum darbouxEnvelope finiteMesh regulatedFunction
      realSeal transport replay provenance localName =>
      [riemannSum, darbouxEnvelope, finiteMesh, regulatedFunction, realSeal, transport, replay,
        provenance, localName]

def RiemannSumConsistencyTasteGate_single_carrier_alignment_toEventFlow :
    RiemannSumConsistencyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RiemannSumConsistencyTasteGate_single_carrier_alignment_fields x).map
      riemannSumConsistencyEncodeBHist

def RiemannSumConsistencyTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RiemannSumConsistencyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | riemannSum :: darbouxEnvelope :: finiteMesh :: regulatedFunction :: realSeal :: transport ::
      replay :: provenance :: localName :: [] =>
      some
        (RiemannSumConsistencyUp.mk
          (riemannSumConsistencyDecodeBHist riemannSum)
          (riemannSumConsistencyDecodeBHist darbouxEnvelope)
          (riemannSumConsistencyDecodeBHist finiteMesh)
          (riemannSumConsistencyDecodeBHist regulatedFunction)
          (riemannSumConsistencyDecodeBHist realSeal)
          (riemannSumConsistencyDecodeBHist transport)
          (riemannSumConsistencyDecodeBHist replay)
          (riemannSumConsistencyDecodeBHist provenance)
          (riemannSumConsistencyDecodeBHist localName))
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier :
    BHistCarrier RiemannSumConsistencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RiemannSumConsistencyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RiemannSumConsistencyTasteGate_single_carrier_alignment_fromEventFlow

instance RiemannSumConsistencyTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RiemannSumConsistencyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier

private theorem RiemannSumConsistencyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannSumConsistencyUp,
      @BHistCarrier.fromEventFlow RiemannSumConsistencyUp
          RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier
          (@BHistCarrier.toEventFlow RiemannSumConsistencyUp
            RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk riemannSum darbouxEnvelope finiteMesh regulatedFunction realSeal transport replay
      provenance localName =>
      change
        some
            (RiemannSumConsistencyUp.mk
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist riemannSum))
              (riemannSumConsistencyDecodeBHist
                (riemannSumConsistencyEncodeBHist darbouxEnvelope))
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist finiteMesh))
              (riemannSumConsistencyDecodeBHist
                (riemannSumConsistencyEncodeBHist regulatedFunction))
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist realSeal))
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist transport))
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist replay))
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist provenance))
              (riemannSumConsistencyDecodeBHist (riemannSumConsistencyEncodeBHist localName))) =
          some
            (RiemannSumConsistencyUp.mk riemannSum darbouxEnvelope finiteMesh regulatedFunction
              realSeal transport replay provenance localName)
      rw [RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode riemannSum,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode darbouxEnvelope,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode finiteMesh,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode regulatedFunction,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode realSeal,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode transport,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode replay,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode provenance,
        RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode localName]

private theorem RiemannSumConsistencyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannSumConsistencyUp} :
    @BHistCarrier.toEventFlow RiemannSumConsistencyUp
        RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier x =
      @BHistCarrier.toEventFlow RiemannSumConsistencyUp
        RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          @BHistCarrier.fromEventFlow RiemannSumConsistencyUp
              RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier
              (@BHistCarrier.toEventFlow RiemannSumConsistencyUp
                RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier x) :=
        (RiemannSumConsistencyTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          @BHistCarrier.fromEventFlow RiemannSumConsistencyUp
              RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier
              (@BHistCarrier.toEventFlow RiemannSumConsistencyUp
                RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier y) :=
        congrArg
          (@BHistCarrier.fromEventFlow RiemannSumConsistencyUp
            RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier) hxy
      _ = some y := RiemannSumConsistencyTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def RiemannSumConsistencyTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate RiemannSumConsistencyUp
      RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact RiemannSumConsistencyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannSumConsistencyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RiemannSumConsistencyTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RiemannSumConsistencyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RiemannSumConsistencyTasteGate_single_carrier_alignment_gate

theorem RiemannSumConsistencyTasteGate_single_carrier_alignment :
    (forall h : BHist, riemannSumConsistencyDecodeBHist
      (riemannSumConsistencyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RiemannSumConsistencyUp) ∧
      Nonempty (ChapterTasteGate RiemannSumConsistencyUp) ∧
      riemannSumConsistencyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RiemannSumConsistencyTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨RiemannSumConsistencyTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨RiemannSumConsistencyTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.RiemannSumConsistencyUp
