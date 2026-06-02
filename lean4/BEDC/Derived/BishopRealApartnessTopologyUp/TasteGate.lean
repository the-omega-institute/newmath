import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealApartnessTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealApartnessTopologyUp : Type where
  | mk (R A L T W Q O H C P N : BHist) : BishopRealApartnessTopologyUp
  deriving DecidableEq

def bishopRealApartnessTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealApartnessTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealApartnessTopologyEncodeBHist h

def bishopRealApartnessTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealApartnessTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealApartnessTopologyDecodeBHist tail)

private theorem BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopRealApartnessTopologyDecodeBHist
        (bishopRealApartnessTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealApartnessTopologyFields :
    BishopRealApartnessTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealApartnessTopologyUp.mk R A L T W Q O H C P N =>
      [R, A, L, T, W, Q, O, H, C, P, N]

def bishopRealApartnessTopologyToEventFlow :
    BishopRealApartnessTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopRealApartnessTopologyFields x).map
        bishopRealApartnessTopologyEncodeBHist

private def bishopRealApartnessTopologyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealApartnessTopologyEventAt index rest

def bishopRealApartnessTopologyFromEventFlow
    (ef : EventFlow) : Option BishopRealApartnessTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealApartnessTopologyUp.mk
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 0 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 1 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 2 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 3 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 4 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 5 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 6 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 7 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 8 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 9 ef))
      (bishopRealApartnessTopologyDecodeBHist (bishopRealApartnessTopologyEventAt 10 ef)))

private theorem BishopRealApartnessTopologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealApartnessTopologyUp,
      bishopRealApartnessTopologyFromEventFlow
        (bishopRealApartnessTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A L T W Q O H C P N =>
      change
        some
          (BishopRealApartnessTopologyUp.mk
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist R))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist A))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist L))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist T))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist W))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist Q))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist O))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist H))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist C))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist P))
            (bishopRealApartnessTopologyDecodeBHist
              (bishopRealApartnessTopologyEncodeBHist N))) =
          some (BishopRealApartnessTopologyUp.mk R A L T W Q O H C P N)
      rw [BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode R,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode A,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode L,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode T,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode W,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode Q,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode O,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode H,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode C,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode P,
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRealApartnessTopologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealApartnessTopologyUp} :
    bishopRealApartnessTopologyToEventFlow x = bishopRealApartnessTopologyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealApartnessTopologyFromEventFlow (bishopRealApartnessTopologyToEventFlow x) =
        bishopRealApartnessTopologyFromEventFlow (bishopRealApartnessTopologyToEventFlow y) :=
    congrArg bishopRealApartnessTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealApartnessTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealApartnessTopologyTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopRealApartnessTopologyTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopRealApartnessTopologyUp,
      bishopRealApartnessTopologyFields x = bishopRealApartnessTopologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ A₁ L₁ T₁ W₁ Q₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ A₂ L₂ T₂ W₂ Q₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopRealApartnessTopologyBHistCarrier :
    BHistCarrier BishopRealApartnessTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealApartnessTopologyToEventFlow
  fromEventFlow := bishopRealApartnessTopologyFromEventFlow

instance bishopRealApartnessTopologyChapterTasteGate :
    ChapterTasteGate BishopRealApartnessTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealApartnessTopologyFromEventFlow
        (bishopRealApartnessTopologyToEventFlow x) = some x
    exact BishopRealApartnessTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealApartnessTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopRealApartnessTopologyFieldFaithful :
    FieldFaithful BishopRealApartnessTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealApartnessTopologyFields
  field_faithful := BishopRealApartnessTopologyTasteGate_single_carrier_alignment_fields

instance bishopRealApartnessTopologyNontrivial :
    Nontrivial BishopRealApartnessTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRealApartnessTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRealApartnessTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopRealApartnessTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRealApartnessTopologyChapterTasteGate

theorem BishopRealApartnessTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRealApartnessTopologyDecodeBHist
        (bishopRealApartnessTopologyEncodeBHist h) = h) ∧
      (∀ x : BishopRealApartnessTopologyUp,
        bishopRealApartnessTopologyFromEventFlow
          (bishopRealApartnessTopologyToEventFlow x) = some x) ∧
        (∀ x y : BishopRealApartnessTopologyUp,
          bishopRealApartnessTopologyToEventFlow x =
              bishopRealApartnessTopologyToEventFlow y → x = y) ∧
          bishopRealApartnessTopologyFields
              (BishopRealApartnessTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BishopRealApartnessTopologyTasteGate_single_carrier_alignment_decode_encode,
      BishopRealApartnessTopologyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopRealApartnessTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopRealApartnessTopologyUp
