import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorPairingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorPairingUp : Type where
  | mk (X Y J L R H C P N : BHist) : CantorPairingUp
  deriving DecidableEq

def cantorPairingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorPairingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorPairingEncodeBHist h

def cantorPairingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorPairingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorPairingDecodeBHist tail)

private theorem CantorPairingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cantorPairingDecodeBHist (cantorPairingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cantorPairingFields : CantorPairingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorPairingUp.mk X Y J L R H C P N => [X, Y, J, L, R, H, C, P, N]

def cantorPairingToEventFlow : CantorPairingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cantorPairingFields x).map cantorPairingEncodeBHist

private def cantorPairingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorPairingEventAt index rest

def cantorPairingFromEventFlow (ef : EventFlow) : Option CantorPairingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CantorPairingUp.mk
      (cantorPairingDecodeBHist (cantorPairingEventAt 0 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 1 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 2 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 3 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 4 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 5 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 6 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 7 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAt 8 ef)))

private theorem CantorPairingTasteGate_single_carrier_alignment_round_trip
    (x : CantorPairingUp) :
    cantorPairingFromEventFlow (cantorPairingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y J L R H C P N =>
      change
        some
          (CantorPairingUp.mk
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist X))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist Y))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist J))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist L))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist R))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist H))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist C))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist P))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist N))) =
          some (CantorPairingUp.mk X Y J L R H C P N)
      rw [CantorPairingTasteGate_single_carrier_alignment_decode_encode X,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode Y,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode J,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode L,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode R,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode H,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode C,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode P,
        CantorPairingTasteGate_single_carrier_alignment_decode_encode N]

private theorem CantorPairingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorPairingUp} :
    cantorPairingToEventFlow x = cantorPairingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorPairingFromEventFlow (cantorPairingToEventFlow x) =
        cantorPairingFromEventFlow (cantorPairingToEventFlow y) :=
    congrArg cantorPairingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CantorPairingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CantorPairingTasteGate_single_carrier_alignment_round_trip y)))

private theorem CantorPairingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CantorPairingUp, cantorPairingFields x = cantorPairingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ J₁ L₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ J₂ L₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cantorPairingBHistCarrier : BHistCarrier CantorPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorPairingToEventFlow
  fromEventFlow := cantorPairingFromEventFlow

instance cantorPairingChapterTasteGate : ChapterTasteGate CantorPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorPairingFromEventFlow (cantorPairingToEventFlow x) = some x
    exact CantorPairingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorPairingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cantorPairingFieldFaithful : FieldFaithful CantorPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorPairingFields
  field_faithful := CantorPairingTasteGate_single_carrier_alignment_fields_faithful

instance cantorPairingNontrivial : BEDC.Meta.TasteGate.Nontrivial CantorPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorPairingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorPairingUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CantorPairingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorPairingChapterTasteGate

theorem CantorPairingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CantorPairingUp) ∧
      Nonempty (FieldFaithful CantorPairingUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CantorPairingUp) ∧
          (∀ h : BHist, cantorPairingDecodeBHist (cantorPairingEncodeBHist h) = h) ∧
            (∀ x : CantorPairingUp,
              cantorPairingFromEventFlow (cantorPairingToEventFlow x) = some x) ∧
              (∀ x y : CantorPairingUp,
                cantorPairingToEventFlow x = cantorPairingToEventFlow y -> x = y) ∧
                cantorPairingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cantorPairingChapterTasteGate⟩,
      ⟨cantorPairingFieldFaithful⟩,
      ⟨cantorPairingNontrivial⟩,
      CantorPairingTasteGate_single_carrier_alignment_decode_encode,
      CantorPairingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CantorPairingTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CantorPairingUp
