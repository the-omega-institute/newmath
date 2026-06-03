import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformEntourageBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformEntourageBasisUp : Type where
  | mk (pointSource basisLedger diagonal refinement symmetry composition transport replay
      provenance localName : BHist) : UniformEntourageBasisUp
  deriving DecidableEq

def uniformEntourageBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformEntourageBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformEntourageBasisEncodeBHist h

def uniformEntourageBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformEntourageBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformEntourageBasisDecodeBHist tail)

private theorem UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def UniformEntourageBasisTasteGate_single_carrier_alignment_fields :
    UniformEntourageBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformEntourageBasisUp.mk pointSource basisLedger diagonal refinement symmetry
      composition transport replay provenance localName =>
      [pointSource, basisLedger, diagonal, refinement, symmetry, composition, transport, replay,
        provenance, localName]

def UniformEntourageBasisTasteGate_single_carrier_alignment_toEventFlow :
    UniformEntourageBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (UniformEntourageBasisTasteGate_single_carrier_alignment_fields x).map
      uniformEntourageBasisEncodeBHist

def UniformEntourageBasisTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option UniformEntourageBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | pointSource :: basisLedger :: diagonal :: refinement :: symmetry :: composition ::
        transport :: replay :: provenance :: localName :: [] =>
      some
        (UniformEntourageBasisUp.mk
          (uniformEntourageBasisDecodeBHist pointSource)
          (uniformEntourageBasisDecodeBHist basisLedger)
          (uniformEntourageBasisDecodeBHist diagonal)
          (uniformEntourageBasisDecodeBHist refinement)
          (uniformEntourageBasisDecodeBHist symmetry)
          (uniformEntourageBasisDecodeBHist composition)
          (uniformEntourageBasisDecodeBHist transport)
          (uniformEntourageBasisDecodeBHist replay)
          (uniformEntourageBasisDecodeBHist provenance)
              (uniformEntourageBasisDecodeBHist localName))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def UniformEntourageBasisTasteGate_single_carrier_alignment_carrier :
    BHistCarrier UniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := UniformEntourageBasisTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := UniformEntourageBasisTasteGate_single_carrier_alignment_fromEventFlow

instance UniformEntourageBasisTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier UniformEntourageBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniformEntourageBasisTasteGate_single_carrier_alignment_carrier

private theorem UniformEntourageBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformEntourageBasisUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk pointSource basisLedger diagonal refinement symmetry composition transport replay
      provenance localName =>
      change
        some
            (UniformEntourageBasisUp.mk
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist pointSource))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist basisLedger))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist diagonal))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist refinement))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist symmetry))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist composition))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist transport))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist replay))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist provenance))
              (uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist localName))) =
          some
            (UniformEntourageBasisUp.mk pointSource basisLedger diagonal refinement symmetry
              composition transport replay provenance localName)
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode pointSource]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode basisLedger]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode diagonal]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode refinement]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode symmetry]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode composition]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode transport]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode replay]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode localName]

private theorem UniformEntourageBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformEntourageBasisUp} :
    BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) :=
        (UniformEntourageBasisTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow y) :=
        congrArg BHistCarrier.fromEventFlow hxy
      _ = some y := UniformEntourageBasisTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def UniformEntourageBasisTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate UniformEntourageBasisUp
      UniformEntourageBasisTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact UniformEntourageBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformEntourageBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance UniformEntourageBasisTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate UniformEntourageBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniformEntourageBasisTasteGate_single_carrier_alignment_gate

theorem UniformEntourageBasisTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformEntourageBasisDecodeBHist (uniformEntourageBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformEntourageBasisUp) ∧
      Nonempty (ChapterTasteGate UniformEntourageBasisUp) ∧
      uniformEntourageBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformEntourageBasisTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨UniformEntourageBasisTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨UniformEntourageBasisTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.UniformEntourageBasisUp
