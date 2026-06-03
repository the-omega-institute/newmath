import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteMetricEntropyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteMetricEntropyUp : Type where
  | mk (X epsilon C Pk L H Cn Q N : BHist) : FiniteMetricEntropyUp

def finiteMetricEntropyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteMetricEntropyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteMetricEntropyEncodeBHist h

def finiteMetricEntropyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteMetricEntropyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteMetricEntropyDecodeBHist tail)

private theorem FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteMetricEntropyFields : FiniteMetricEntropyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMetricEntropyUp.mk X epsilon C Pk L H Cn Q N =>
      [X, epsilon, C, Pk, L, H, Cn, Q, N]

def finiteMetricEntropyToEventFlow : FiniteMetricEntropyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteMetricEntropyFields x).map finiteMetricEntropyEncodeBHist

def finiteMetricEntropyFromEventFlow : EventFlow → Option FiniteMetricEntropyUp :=
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
    | X :: epsilon :: C :: Pk :: L :: H :: Cn :: Q :: N :: [] =>
      some
        (FiniteMetricEntropyUp.mk
          (finiteMetricEntropyDecodeBHist X)
          (finiteMetricEntropyDecodeBHist epsilon)
          (finiteMetricEntropyDecodeBHist C)
          (finiteMetricEntropyDecodeBHist Pk)
          (finiteMetricEntropyDecodeBHist L)
          (finiteMetricEntropyDecodeBHist H)
          (finiteMetricEntropyDecodeBHist Cn)
          (finiteMetricEntropyDecodeBHist Q)
          (finiteMetricEntropyDecodeBHist N))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def finiteMetricEntropyCarrier : BHistCarrier FiniteMetricEntropyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteMetricEntropyToEventFlow
  fromEventFlow := finiteMetricEntropyFromEventFlow

instance finiteMetricEntropyBHistCarrier : BHistCarrier FiniteMetricEntropyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteMetricEntropyCarrier

private theorem FiniteMetricEntropyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteMetricEntropyUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X epsilon C Pk L H Cn Q N =>
      change
        some
            (FiniteMetricEntropyUp.mk
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist X))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist epsilon))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist C))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist Pk))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist L))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist H))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist Cn))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist Q))
              (finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist N))) =
          some (FiniteMetricEntropyUp.mk X epsilon C Pk L H Cn Q N)
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode X]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode epsilon]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode C]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode Pk]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode L]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode H]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode Cn]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode Q]
      rw [FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteMetricEntropyTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : FiniteMetricEntropyUp} :
    BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) :=
        (FiniteMetricEntropyTasteGate_single_carrier_alignment_round_trip x).symm
      _ = BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow y) :=
        congrArg BHistCarrier.fromEventFlow hxy
      _ = some y := FiniteMetricEntropyTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def finiteMetricEntropyGate : @ChapterTasteGate FiniteMetricEntropyUp finiteMetricEntropyCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact FiniteMetricEntropyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteMetricEntropyTasteGate_single_carrier_alignment_ToEventFlow_injective heq)

instance finiteMetricEntropyChapterTasteGate : ChapterTasteGate FiniteMetricEntropyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteMetricEntropyGate

theorem FiniteMetricEntropyTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteMetricEntropyDecodeBHist (finiteMetricEntropyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteMetricEntropyUp) ∧
        Nonempty (ChapterTasteGate FiniteMetricEntropyUp) ∧
          finiteMetricEntropyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteMetricEntropyTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨finiteMetricEntropyCarrier⟩, ⟨⟨finiteMetricEntropyGate⟩, rfl⟩⟩⟩

end BEDC.Derived.FiniteMetricEntropyUp
