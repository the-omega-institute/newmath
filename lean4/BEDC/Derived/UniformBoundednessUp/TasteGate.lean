import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformBoundednessUp : Type where
  | mk (F W B N R S Q H C P L : BHist) : UniformBoundednessUp
  deriving DecidableEq

def uniformBoundednessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformBoundednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformBoundednessEncodeBHist h

def uniformBoundednessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformBoundednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformBoundednessDecodeBHist tail)

private theorem UniformBoundednessUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformBoundednessFields : UniformBoundednessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformBoundednessUp.mk F W B N R S Q H C P L => [F, W, B, N, R, S, Q, H, C, P, L]

def uniformBoundednessToEventFlow : UniformBoundednessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map uniformBoundednessEncodeBHist (uniformBoundednessFields x)

private def uniformBoundednessEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformBoundednessEventAtDefault index rest

def uniformBoundednessFromEventFlow (ef : EventFlow) : Option UniformBoundednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformBoundednessUp.mk
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 0 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 1 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 2 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 3 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 4 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 5 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 6 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 7 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 8 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 9 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 10 ef)))

private theorem UniformBoundednessUpTasteGate_single_carrier_alignment_round_trip :
    forall x : UniformBoundednessUp,
      uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W B N R S Q H C P L =>
      change
        some
          (UniformBoundednessUp.mk
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist F))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist W))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist B))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist N))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist R))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist S))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist Q))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist H))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist C))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist P))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist L))) =
          some (UniformBoundednessUp.mk F W B N R S Q H C P L)
      rw [UniformBoundednessUpTasteGate_single_carrier_alignment_decode F,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode W,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode B,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode N,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode R,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode S,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode Q,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode H,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode C,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode P,
        UniformBoundednessUpTasteGate_single_carrier_alignment_decode L]

private theorem UniformBoundednessUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformBoundednessUp} :
    uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) =
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow y) :=
    congrArg uniformBoundednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformBoundednessUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformBoundednessUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformBoundednessUpTasteGate_single_carrier_alignment_fields :
    forall x y : UniformBoundednessUp,
      uniformBoundednessFields x = uniformBoundednessFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 W1 B1 N1 R1 S1 Q1 H1 C1 P1 L1 =>
      cases y with
      | mk F2 W2 B2 N2 R2 S2 Q2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance uniformBoundednessBHistCarrier : BHistCarrier UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformBoundednessToEventFlow
  fromEventFlow := uniformBoundednessFromEventFlow

instance uniformBoundednessChapterTasteGate : ChapterTasteGate UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x
    exact UniformBoundednessUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformBoundednessUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformBoundednessFieldFaithful : FieldFaithful UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformBoundednessFields
  field_faithful := UniformBoundednessUpTasteGate_single_carrier_alignment_fields

instance uniformBoundednessNontrivial : Nontrivial UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformBoundednessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformBoundednessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformBoundednessUpTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h) /\
      (forall x : UniformBoundednessUp,
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x) /\
        (forall x y : UniformBoundednessUp,
          uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y -> x = y) /\
          uniformBoundednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨UniformBoundednessUpTasteGate_single_carrier_alignment_decode,
      UniformBoundednessUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformBoundednessUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

theorem UniformBoundednessTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h) /\
      (forall x : UniformBoundednessUp,
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x) /\
        (forall x y : UniformBoundednessUp,
          uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y -> x = y) /\
          uniformBoundednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact UniformBoundednessUpTasteGate_single_carrier_alignment

end BEDC.Derived.UniformBoundednessUp
