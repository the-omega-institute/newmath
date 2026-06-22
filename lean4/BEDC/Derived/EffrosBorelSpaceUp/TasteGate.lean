import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffrosBorelSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffrosBorelSpaceUp : Type where
  | mk (H A M V K D T C P N : BHist) : EffrosBorelSpaceUp
  deriving DecidableEq

def effrosBorelSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effrosBorelSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effrosBorelSpaceEncodeBHist h

def effrosBorelSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effrosBorelSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effrosBorelSpaceDecodeBHist tail)

private theorem effrosBorelSpace_decode_encode_bhist :
    ∀ h : BHist, effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effrosBorelSpaceFields : EffrosBorelSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffrosBorelSpaceUp.mk H A M V K D T C P N => [H, A, M, V, K, D, T, C, P, N]

def effrosBorelSpaceToEventFlow : EffrosBorelSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (effrosBorelSpaceFields x).map effrosBorelSpaceEncodeBHist

private def effrosBorelSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effrosBorelSpaceEventAt index rest

def effrosBorelSpaceFromEventFlow (ef : EventFlow) : Option EffrosBorelSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffrosBorelSpaceUp.mk
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 0 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 1 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 2 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 3 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 4 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 5 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 6 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 7 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 8 ef))
      (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEventAt 9 ef)))

private theorem effrosBorelSpace_round_trip (x : EffrosBorelSpaceUp) :
    effrosBorelSpaceFromEventFlow (effrosBorelSpaceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H A M V K D T C P N =>
      change
        some
          (EffrosBorelSpaceUp.mk
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist H))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist A))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist M))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist V))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist K))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist D))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist T))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist C))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist P))
            (effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist N))) =
          some (EffrosBorelSpaceUp.mk H A M V K D T C P N)
      rw [effrosBorelSpace_decode_encode_bhist H,
        effrosBorelSpace_decode_encode_bhist A,
        effrosBorelSpace_decode_encode_bhist M,
        effrosBorelSpace_decode_encode_bhist V,
        effrosBorelSpace_decode_encode_bhist K,
        effrosBorelSpace_decode_encode_bhist D,
        effrosBorelSpace_decode_encode_bhist T,
        effrosBorelSpace_decode_encode_bhist C,
        effrosBorelSpace_decode_encode_bhist P,
        effrosBorelSpace_decode_encode_bhist N]

private theorem effrosBorelSpaceToEventFlow_injective {x y : EffrosBorelSpaceUp} :
    effrosBorelSpaceToEventFlow x = effrosBorelSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effrosBorelSpaceFromEventFlow (effrosBorelSpaceToEventFlow x) =
        effrosBorelSpaceFromEventFlow (effrosBorelSpaceToEventFlow y) :=
    congrArg effrosBorelSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effrosBorelSpace_round_trip x).symm
      (Eq.trans hread (effrosBorelSpace_round_trip y)))

private theorem effrosBorelSpace_fields_faithful :
    ∀ x y : EffrosBorelSpaceUp,
      effrosBorelSpaceFields x = effrosBorelSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H A M V K D T C P N =>
      cases y with
      | mk H' A' M' V' K' D' T' C' P' N' =>
          cases hfields
          rfl

instance effrosBorelSpaceBHistCarrier : BHistCarrier EffrosBorelSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effrosBorelSpaceToEventFlow
  fromEventFlow := effrosBorelSpaceFromEventFlow

instance effrosBorelSpaceChapterTasteGate :
    ChapterTasteGate EffrosBorelSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effrosBorelSpaceFromEventFlow (effrosBorelSpaceToEventFlow x) = some x
    exact effrosBorelSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effrosBorelSpaceToEventFlow_injective heq)

instance effrosBorelSpaceFieldFaithful : FieldFaithful EffrosBorelSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effrosBorelSpaceFields
  field_faithful := effrosBorelSpace_fields_faithful

instance effrosBorelSpaceNontrivial : Nontrivial EffrosBorelSpaceUp where
  witness_pair :=
    ⟨EffrosBorelSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EffrosBorelSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem EffrosBorelSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, effrosBorelSpaceDecodeBHist (effrosBorelSpaceEncodeBHist h) = h) ∧
      (∀ x : EffrosBorelSpaceUp,
        effrosBorelSpaceFromEventFlow (effrosBorelSpaceToEventFlow x) = some x) ∧
      (∀ x y : EffrosBorelSpaceUp,
        effrosBorelSpaceToEventFlow x = effrosBorelSpaceToEventFlow y → x = y) ∧
      effrosBorelSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨effrosBorelSpace_decode_encode_bhist,
    effrosBorelSpace_round_trip,
    fun _ _ heq => effrosBorelSpaceToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.EffrosBorelSpaceUp
