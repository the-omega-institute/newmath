import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSineUp : Type where
  | mk (A F B U M K P E Q H C L N : BHist) : RealSineUp
  deriving DecidableEq

def realSineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSineEncodeBHist h

def realSineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSineDecodeBHist tail)

private theorem RealSineTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realSineDecodeBHist (realSineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def realSineFields : RealSineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSineUp.mk A F B U M K P E Q H C L N => [A, F, B, U, M, K, P, E, Q, H, C, L, N]

def realSineToEventFlow : RealSineUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realSineFields x).map realSineEncodeBHist

private def realSineEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realSineEventAtDefault index rest

def realSineFromEventFlow (ef : EventFlow) : Option RealSineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealSineUp.mk
      (realSineDecodeBHist (realSineEventAtDefault 0 ef))
      (realSineDecodeBHist (realSineEventAtDefault 1 ef))
      (realSineDecodeBHist (realSineEventAtDefault 2 ef))
      (realSineDecodeBHist (realSineEventAtDefault 3 ef))
      (realSineDecodeBHist (realSineEventAtDefault 4 ef))
      (realSineDecodeBHist (realSineEventAtDefault 5 ef))
      (realSineDecodeBHist (realSineEventAtDefault 6 ef))
      (realSineDecodeBHist (realSineEventAtDefault 7 ef))
      (realSineDecodeBHist (realSineEventAtDefault 8 ef))
      (realSineDecodeBHist (realSineEventAtDefault 9 ef))
      (realSineDecodeBHist (realSineEventAtDefault 10 ef))
      (realSineDecodeBHist (realSineEventAtDefault 11 ef))
      (realSineDecodeBHist (realSineEventAtDefault 12 ef)))

private theorem RealSineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealSineUp, realSineFromEventFlow (realSineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A F B U M K P E Q H C L N =>
      change
        some
          (RealSineUp.mk
            (realSineDecodeBHist (realSineEncodeBHist A))
            (realSineDecodeBHist (realSineEncodeBHist F))
            (realSineDecodeBHist (realSineEncodeBHist B))
            (realSineDecodeBHist (realSineEncodeBHist U))
            (realSineDecodeBHist (realSineEncodeBHist M))
            (realSineDecodeBHist (realSineEncodeBHist K))
            (realSineDecodeBHist (realSineEncodeBHist P))
            (realSineDecodeBHist (realSineEncodeBHist E))
            (realSineDecodeBHist (realSineEncodeBHist Q))
            (realSineDecodeBHist (realSineEncodeBHist H))
            (realSineDecodeBHist (realSineEncodeBHist C))
            (realSineDecodeBHist (realSineEncodeBHist L))
            (realSineDecodeBHist (realSineEncodeBHist N))) =
          some (RealSineUp.mk A F B U M K P E Q H C L N)
      rw [RealSineTasteGate_single_carrier_alignment_decode A,
        RealSineTasteGate_single_carrier_alignment_decode F,
        RealSineTasteGate_single_carrier_alignment_decode B,
        RealSineTasteGate_single_carrier_alignment_decode U,
        RealSineTasteGate_single_carrier_alignment_decode M,
        RealSineTasteGate_single_carrier_alignment_decode K,
        RealSineTasteGate_single_carrier_alignment_decode P,
        RealSineTasteGate_single_carrier_alignment_decode E,
        RealSineTasteGate_single_carrier_alignment_decode Q,
        RealSineTasteGate_single_carrier_alignment_decode H,
        RealSineTasteGate_single_carrier_alignment_decode C,
        RealSineTasteGate_single_carrier_alignment_decode L,
        RealSineTasteGate_single_carrier_alignment_decode N]

private theorem RealSineTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSineUp} :
    realSineToEventFlow x = realSineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSineFromEventFlow (realSineToEventFlow x) =
        realSineFromEventFlow (realSineToEventFlow y) :=
    congrArg realSineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealSineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSineTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealSineTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealSineUp, realSineFields x = realSineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 F1 B1 U1 M1 K1 P1 E1 Q1 H1 C1 L1 N1 =>
      cases y with
      | mk A2 F2 B2 U2 M2 K2 P2 E2 Q2 H2 C2 L2 N2 =>
          cases hfields
          rfl

instance realSineBHistCarrier : BHistCarrier RealSineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSineToEventFlow
  fromEventFlow := realSineFromEventFlow

instance realSineChapterTasteGate : ChapterTasteGate RealSineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSineFromEventFlow (realSineToEventFlow x) = some x
    exact RealSineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealSineTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realSineFieldFaithful : FieldFaithful RealSineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSineFields
  field_faithful := RealSineTasteGate_single_carrier_alignment_fields

instance realSineNontrivial : Nontrivial RealSineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealSineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealSineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSineChapterTasteGate

theorem RealSineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealSineUp) ∧
      Nonempty (FieldFaithful RealSineUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealSineUp) ∧
          (∀ h : BHist, realSineDecodeBHist (realSineEncodeBHist h) = h) ∧
            (∀ x : RealSineUp, realSineFromEventFlow (realSineToEventFlow x) = some x) ∧
              (∀ x y : RealSineUp,
                realSineToEventFlow x = realSineToEventFlow y → x = y) ∧
                realSineEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realSineChapterTasteGate⟩,
      ⟨realSineFieldFaithful⟩,
      ⟨realSineNontrivial⟩,
      RealSineTasteGate_single_carrier_alignment_decode,
      RealSineTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealSineTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealSineUp
