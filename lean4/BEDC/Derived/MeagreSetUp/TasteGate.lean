import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeagreSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeagreSetUp : Type where
  | mk (B Q K W R E T H C P N : BHist) : MeagreSetUp
  deriving DecidableEq

def meagreSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: meagreSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: meagreSetEncodeBHist h

def meagreSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (meagreSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (meagreSetDecodeBHist tail)

private theorem meagreSetDecodeEncode :
    ∀ h : BHist, meagreSetDecodeBHist (meagreSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def meagreSetFields : MeagreSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeagreSetUp.mk B Q K W R E T H C P N => [B, Q, K, W, R, E, T, H, C, P, N]

def meagreSetToEventFlow : MeagreSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (meagreSetFields x).map meagreSetEncodeBHist

private def meagreSetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => meagreSetEventAt index rest

def meagreSetFromEventFlow : EventFlow → Option MeagreSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MeagreSetUp.mk
          (meagreSetDecodeBHist (meagreSetEventAt 0 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 1 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 2 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 3 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 4 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 5 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 6 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 7 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 8 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 9 ef))
          (meagreSetDecodeBHist (meagreSetEventAt 10 ef)))

private theorem meagreSetRoundTrip :
    ∀ x : MeagreSetUp, meagreSetFromEventFlow (meagreSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Q K W R E T H C P N =>
      change
        some
          (MeagreSetUp.mk
            (meagreSetDecodeBHist (meagreSetEncodeBHist B))
            (meagreSetDecodeBHist (meagreSetEncodeBHist Q))
            (meagreSetDecodeBHist (meagreSetEncodeBHist K))
            (meagreSetDecodeBHist (meagreSetEncodeBHist W))
            (meagreSetDecodeBHist (meagreSetEncodeBHist R))
            (meagreSetDecodeBHist (meagreSetEncodeBHist E))
            (meagreSetDecodeBHist (meagreSetEncodeBHist T))
            (meagreSetDecodeBHist (meagreSetEncodeBHist H))
            (meagreSetDecodeBHist (meagreSetEncodeBHist C))
            (meagreSetDecodeBHist (meagreSetEncodeBHist P))
            (meagreSetDecodeBHist (meagreSetEncodeBHist N))) =
          some (MeagreSetUp.mk B Q K W R E T H C P N)
      rw [meagreSetDecodeEncode B, meagreSetDecodeEncode Q, meagreSetDecodeEncode K,
        meagreSetDecodeEncode W, meagreSetDecodeEncode R, meagreSetDecodeEncode E,
        meagreSetDecodeEncode T, meagreSetDecodeEncode H, meagreSetDecodeEncode C,
        meagreSetDecodeEncode P, meagreSetDecodeEncode N]

private theorem meagreSetToEventFlow_injective {x y : MeagreSetUp} :
    meagreSetToEventFlow x = meagreSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      meagreSetFromEventFlow (meagreSetToEventFlow x) =
        meagreSetFromEventFlow (meagreSetToEventFlow y) :=
    congrArg meagreSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (meagreSetRoundTrip x).symm (Eq.trans hread (meagreSetRoundTrip y)))

private theorem meagreSetFields_injective :
    ∀ x y : MeagreSetUp, meagreSetFields x = meagreSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ Q₁ K₁ W₁ R₁ E₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ Q₂ K₂ W₂ R₂ E₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance meagreSetBHistCarrier : BHistCarrier MeagreSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := meagreSetToEventFlow
  fromEventFlow := meagreSetFromEventFlow

instance meagreSetChapterTasteGate : ChapterTasteGate MeagreSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change meagreSetFromEventFlow (meagreSetToEventFlow x) = some x
    exact meagreSetRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (meagreSetToEventFlow_injective heq)

instance meagreSetFieldFaithful : FieldFaithful MeagreSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := meagreSetFields
  field_faithful := meagreSetFields_injective

instance meagreSetNontrivial : Nontrivial MeagreSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MeagreSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MeagreSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MeagreSetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MeagreSetUp) ∧ Nonempty (FieldFaithful MeagreSetUp) ∧
      Nonempty (Nontrivial MeagreSetUp) ∧
        BHistCarrier.toEventFlow
            (MeagreSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          meagreSetToEventFlow
            (MeagreSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact ⟨⟨meagreSetChapterTasteGate⟩, ⟨meagreSetFieldFaithful⟩, ⟨meagreSetNontrivial⟩, rfl⟩

end BEDC.Derived.MeagreSetUp
