import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FellTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FellTopologyUp : Type where
  | mk (H L U V K W S C P N : BHist) : FellTopologyUp
  deriving DecidableEq

def fellTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fellTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fellTopologyEncodeBHist h

def fellTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fellTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fellTopologyDecodeBHist tail)

private theorem FellTopologyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, fellTopologyDecodeBHist (fellTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fellTopologyFields : FellTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FellTopologyUp.mk H L U V K W S C P N => [H, L, U, V, K, W, S, C, P, N]

def fellTopologyToEventFlow : FellTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fellTopologyFields x).map fellTopologyEncodeBHist

private def fellTopologyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fellTopologyEventAt index rest

def fellTopologyFromEventFlow (ef : EventFlow) : Option FellTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FellTopologyUp.mk
      (fellTopologyDecodeBHist (fellTopologyEventAt 0 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 1 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 2 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 3 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 4 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 5 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 6 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 7 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 8 ef))
      (fellTopologyDecodeBHist (fellTopologyEventAt 9 ef)))

private theorem FellTopologyTasteGate_single_carrier_alignment_round_trip
    (x : FellTopologyUp) :
    fellTopologyFromEventFlow (fellTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H L U V K W S C P N =>
      change
        some
          (FellTopologyUp.mk
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist H))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist L))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist U))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist V))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist K))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist W))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist S))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist C))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist P))
            (fellTopologyDecodeBHist (fellTopologyEncodeBHist N))) =
          some (FellTopologyUp.mk H L U V K W S C P N)
      rw [FellTopologyTasteGate_single_carrier_alignment_decode H,
        FellTopologyTasteGate_single_carrier_alignment_decode L,
        FellTopologyTasteGate_single_carrier_alignment_decode U,
        FellTopologyTasteGate_single_carrier_alignment_decode V,
        FellTopologyTasteGate_single_carrier_alignment_decode K,
        FellTopologyTasteGate_single_carrier_alignment_decode W,
        FellTopologyTasteGate_single_carrier_alignment_decode S,
        FellTopologyTasteGate_single_carrier_alignment_decode C,
        FellTopologyTasteGate_single_carrier_alignment_decode P,
        FellTopologyTasteGate_single_carrier_alignment_decode N]

private theorem FellTopologyTasteGate_single_carrier_alignment_fields :
    ∀ x y : FellTopologyUp, fellTopologyFields x = fellTopologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ L₁ U₁ V₁ K₁ W₁ S₁ C₁ P₁ N₁ =>
      cases y with
      | mk H₂ L₂ U₂ V₂ K₂ W₂ S₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance fellTopologyBHistCarrier : BHistCarrier FellTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fellTopologyToEventFlow
  fromEventFlow := fellTopologyFromEventFlow

instance fellTopologyFieldFaithful : FieldFaithful FellTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fellTopologyFields
  field_faithful := FellTopologyTasteGate_single_carrier_alignment_fields

instance fellTopologyChapterTasteGate : ChapterTasteGate FellTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fellTopologyFromEventFlow (fellTopologyToEventFlow x) = some x
    exact FellTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    have hread :
        fellTopologyFromEventFlow (fellTopologyToEventFlow x) =
          fellTopologyFromEventFlow (fellTopologyToEventFlow y) :=
      congrArg fellTopologyFromEventFlow heq
    exact hxy
      (Option.some.inj
        (Eq.trans
          (FellTopologyTasteGate_single_carrier_alignment_round_trip x).symm
          (Eq.trans hread
            (FellTopologyTasteGate_single_carrier_alignment_round_trip y))))

instance fellTopologyNontrivial : Nontrivial FellTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FellTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FellTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FellTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, fellTopologyDecodeBHist (fellTopologyEncodeBHist h) = h) ∧
      (∀ x : FellTopologyUp,
        fellTopologyFromEventFlow (fellTopologyToEventFlow x) = some x) ∧
      (∀ x y : FellTopologyUp,
        fellTopologyToEventFlow x = fellTopologyToEventFlow y → x = y) ∧
      fellTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact FellTopologyTasteGate_single_carrier_alignment_decode
  · constructor
    · exact FellTopologyTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        have hread :
            fellTopologyFromEventFlow (fellTopologyToEventFlow x) =
              fellTopologyFromEventFlow (fellTopologyToEventFlow y) :=
          congrArg fellTopologyFromEventFlow heq
        exact Option.some.inj
          (Eq.trans
            (FellTopologyTasteGate_single_carrier_alignment_round_trip x).symm
            (Eq.trans hread
              (FellTopologyTasteGate_single_carrier_alignment_round_trip y)))
      · rfl

end BEDC.Derived.FellTopologyUp
