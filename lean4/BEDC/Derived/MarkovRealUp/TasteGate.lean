import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MarkovRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MarkovRealUp : Type where
  | mk : (C B A S R D E H K P N : BHist) → MarkovRealUp
  deriving DecidableEq

def markovRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: markovRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: markovRealEncodeBHist h

def markovRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (markovRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (markovRealDecodeBHist tail)

theorem MarkovRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, markovRealDecodeBHist (markovRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def markovRealFields : MarkovRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MarkovRealUp.mk C B A S R D E H K P N => [C, B, A, S, R, D, E, H, K, P, N]

def markovRealToEventFlow : MarkovRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MarkovRealUp.mk C B A S R D E H K P N =>
      [markovRealEncodeBHist C,
        markovRealEncodeBHist B,
        markovRealEncodeBHist A,
        markovRealEncodeBHist S,
        markovRealEncodeBHist R,
        markovRealEncodeBHist D,
        markovRealEncodeBHist E,
        markovRealEncodeBHist H,
        markovRealEncodeBHist K,
        markovRealEncodeBHist P,
        markovRealEncodeBHist N]

def markovRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => markovRealEventAt index rest

def markovRealFromEventFlow (ef : EventFlow) : Option MarkovRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MarkovRealUp.mk
      (markovRealDecodeBHist (markovRealEventAt 0 ef))
      (markovRealDecodeBHist (markovRealEventAt 1 ef))
      (markovRealDecodeBHist (markovRealEventAt 2 ef))
      (markovRealDecodeBHist (markovRealEventAt 3 ef))
      (markovRealDecodeBHist (markovRealEventAt 4 ef))
      (markovRealDecodeBHist (markovRealEventAt 5 ef))
      (markovRealDecodeBHist (markovRealEventAt 6 ef))
      (markovRealDecodeBHist (markovRealEventAt 7 ef))
      (markovRealDecodeBHist (markovRealEventAt 8 ef))
      (markovRealDecodeBHist (markovRealEventAt 9 ef))
      (markovRealDecodeBHist (markovRealEventAt 10 ef)))

theorem MarkovRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MarkovRealUp, markovRealFromEventFlow (markovRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C B A S R D E H K P N =>
      change
        some
          (MarkovRealUp.mk
            (markovRealDecodeBHist (markovRealEncodeBHist C))
            (markovRealDecodeBHist (markovRealEncodeBHist B))
            (markovRealDecodeBHist (markovRealEncodeBHist A))
            (markovRealDecodeBHist (markovRealEncodeBHist S))
            (markovRealDecodeBHist (markovRealEncodeBHist R))
            (markovRealDecodeBHist (markovRealEncodeBHist D))
            (markovRealDecodeBHist (markovRealEncodeBHist E))
            (markovRealDecodeBHist (markovRealEncodeBHist H))
            (markovRealDecodeBHist (markovRealEncodeBHist K))
            (markovRealDecodeBHist (markovRealEncodeBHist P))
            (markovRealDecodeBHist (markovRealEncodeBHist N))) =
          some (MarkovRealUp.mk C B A S R D E H K P N)
      rw [MarkovRealTasteGate_single_carrier_alignment_decode_encode C,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode B,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode A,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode S,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode R,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode D,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode E,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode H,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode K,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode P,
        MarkovRealTasteGate_single_carrier_alignment_decode_encode N]

theorem MarkovRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MarkovRealUp} :
    markovRealToEventFlow x = markovRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      markovRealFromEventFlow (markovRealToEventFlow x) =
        markovRealFromEventFlow (markovRealToEventFlow y) :=
    congrArg markovRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MarkovRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MarkovRealTasteGate_single_carrier_alignment_round_trip y)))

theorem MarkovRealTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MarkovRealUp, markovRealFields x = markovRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 B1 A1 S1 R1 D1 E1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 B2 A2 S2 R2 D2 E2 H2 K2 P2 N2 =>
          injection hfields with hC t1
          injection t1 with hB t2
          injection t2 with hA t3
          injection t3 with hS t4
          injection t4 with hR t5
          injection t5 with hD t6
          injection t6 with hE t7
          injection t7 with hH t8
          injection t8 with hK t9
          injection t9 with hP t10
          injection t10 with hN _
          cases hC
          cases hB
          cases hA
          cases hS
          cases hR
          cases hD
          cases hE
          cases hH
          cases hK
          cases hP
          cases hN
          rfl

instance markovRealBHistCarrier : BHistCarrier MarkovRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := markovRealToEventFlow
  fromEventFlow := markovRealFromEventFlow

instance markovRealChapterTasteGate : ChapterTasteGate MarkovRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change markovRealFromEventFlow (markovRealToEventFlow x) = some x
    exact MarkovRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MarkovRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance markovRealFieldFaithful : FieldFaithful MarkovRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := markovRealFields
  field_faithful := MarkovRealTasteGate_single_carrier_alignment_field_faithful

instance markovRealNontrivial : BEDC.Meta.TasteGate.Nontrivial MarkovRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MarkovRealUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MarkovRealUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def markovRealTasteGate : ChapterTasteGate MarkovRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  markovRealChapterTasteGate

theorem MarkovRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, markovRealDecodeBHist (markovRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MarkovRealUp) ∧
        Nonempty (ChapterTasteGate MarkovRealUp) ∧
          Nonempty (FieldFaithful MarkovRealUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial MarkovRealUp) ∧
              markovRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MarkovRealTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨markovRealBHistCarrier⟩
    · constructor
      · exact ⟨markovRealChapterTasteGate⟩
      · constructor
        · exact ⟨markovRealFieldFaithful⟩
        · constructor
          · exact ⟨markovRealNontrivial⟩
          · rfl

end BEDC.Derived.MarkovRealUp
