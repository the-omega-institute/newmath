import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealFieldUp : Type where
  | mk (E R W D F A O H C P N : BHist) : LocatedRealFieldUp
  deriving DecidableEq

def locatedRealFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealFieldEncodeBHist h

def locatedRealFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealFieldDecodeBHist tail)

private theorem LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealFieldFields : LocatedRealFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealFieldUp.mk E R W D F A O H C P N => [E, R, W, D, F, A, O, H, C, P, N]

def locatedRealFieldToEventFlow : LocatedRealFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealFieldFields x).map locatedRealFieldEncodeBHist

private def locatedRealFieldEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealFieldEventAtDefault index rest

def locatedRealFieldFromEventFlow : EventFlow → Option LocatedRealFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedRealFieldUp.mk
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 0 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 1 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 2 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 3 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 4 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 5 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 6 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 7 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 8 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 9 ef))
        (locatedRealFieldDecodeBHist (locatedRealFieldEventAtDefault 10 ef)))

private theorem LocatedRealFieldTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealFieldUp,
      locatedRealFieldFromEventFlow (locatedRealFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E R W D F A O H C P N =>
      change
        some
          (LocatedRealFieldUp.mk
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist E))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist R))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist W))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist D))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist F))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist A))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist O))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist H))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist C))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist P))
            (locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist N))) =
          some (LocatedRealFieldUp.mk E R W D F A O H C P N)
      rw [LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode E,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode R,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode W,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode D,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode F,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode A,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode O,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode H,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode C,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode P,
        LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedRealFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealFieldUp} :
    locatedRealFieldToEventFlow x = locatedRealFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealFieldFromEventFlow (locatedRealFieldToEventFlow x) =
        locatedRealFieldFromEventFlow (locatedRealFieldToEventFlow y) :=
    congrArg locatedRealFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedRealFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedRealFieldTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedRealFieldTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedRealFieldUp, locatedRealFieldFields x = locatedRealFieldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ R₁ W₁ D₁ F₁ A₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ R₂ W₂ D₂ F₂ A₂ O₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hE tail0
          injection tail0 with hR tail1
          injection tail1 with hW tail2
          injection tail2 with hD tail3
          injection tail3 with hF tail4
          injection tail4 with hA tail5
          injection tail5 with hO tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hE
          subst hR
          subst hW
          subst hD
          subst hF
          subst hA
          subst hO
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance locatedRealFieldBHistCarrier : BHistCarrier LocatedRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealFieldToEventFlow
  fromEventFlow := locatedRealFieldFromEventFlow

instance locatedRealFieldChapterTasteGate : ChapterTasteGate LocatedRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealFieldFromEventFlow (locatedRealFieldToEventFlow x) = some x
    exact LocatedRealFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealFieldFieldFaithful : FieldFaithful LocatedRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealFieldFields
  field_faithful := LocatedRealFieldTasteGate_single_carrier_alignment_fields_faithful

instance locatedRealFieldNontrivial : Nontrivial LocatedRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealFieldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealFieldChapterTasteGate

theorem LocatedRealFieldTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRealFieldDecodeBHist (locatedRealFieldEncodeBHist h) = h) ∧
      (∀ x : LocatedRealFieldUp,
        locatedRealFieldFromEventFlow (locatedRealFieldToEventFlow x) = some x) ∧
        (∀ x y : LocatedRealFieldUp,
          locatedRealFieldToEventFlow x = locatedRealFieldToEventFlow y → x = y) ∧
          locatedRealFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨LocatedRealFieldTasteGate_single_carrier_alignment_decode_encode,
      LocatedRealFieldTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedRealFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealFieldUp
