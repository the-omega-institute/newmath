import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRateLatticeUp : Type where
  | mk (A B M J D S R E H C P N : BHist) : CauchyRateLatticeUp
  deriving DecidableEq

def cauchyRateLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateLatticeEncodeBHist h

def cauchyRateLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateLatticeDecodeBHist tail)

private theorem CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateLatticeFields : CauchyRateLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateLatticeUp.mk A B M J D S R E H C P N => [A, B, M, J, D, S, R, E, H, C, P, N]

def cauchyRateLatticeToEventFlow : CauchyRateLatticeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRateLatticeFields x).map cauchyRateLatticeEncodeBHist

private def cauchyRateLatticeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRateLatticeEventAt index rest

def cauchyRateLatticeFromEventFlow (ef : EventFlow) : Option CauchyRateLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRateLatticeUp.mk
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 0 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 1 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 2 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 3 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 4 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 5 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 6 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 7 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 8 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 9 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 10 ef))
      (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEventAt 11 ef)))

private theorem CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRateLatticeUp) :
    cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B M J D S R E H C P N =>
      change
        some
          (CauchyRateLatticeUp.mk
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist A))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist B))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist M))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist J))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist D))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist S))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist R))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist E))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist H))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist C))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist P))
            (cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist N))) =
          some (CauchyRateLatticeUp.mk A B M J D S R E H C P N)
      rw [CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode B,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode M,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode J,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode R,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode E,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRateLatticeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRateLatticeUp} :
    cauchyRateLatticeToEventFlow x = cauchyRateLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow x) =
        cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow y) :=
    congrArg cauchyRateLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRateLatticeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyRateLatticeUp, cauchyRateLatticeFields x = cauchyRateLatticeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ M₁ J₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ M₂ J₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyRateLatticeBHistCarrier : BHistCarrier CauchyRateLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateLatticeToEventFlow
  fromEventFlow := cauchyRateLatticeFromEventFlow

instance cauchyRateLatticeChapterTasteGate : ChapterTasteGate CauchyRateLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow x) = some x
    exact CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRateLatticeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRateLatticeFieldFaithful : FieldFaithful CauchyRateLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRateLatticeFields
  field_faithful := CauchyRateLatticeTasteGate_single_carrier_alignment_fields_faithful

instance cauchyRateLatticeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyRateLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRateLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyRateLatticeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRateLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateLatticeChapterTasteGate

def CauchyRateLatticeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyRateLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateLatticeChapterTasteGate

theorem CauchyRateLatticeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyRateLatticeUp) ∧
      Nonempty (FieldFaithful CauchyRateLatticeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyRateLatticeUp) ∧
          (∀ h : BHist, cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist h) = h) ∧
            (∀ x : CauchyRateLatticeUp,
              cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow x) = some x) ∧
              (∀ x y : CauchyRateLatticeUp,
                cauchyRateLatticeToEventFlow x = cauchyRateLatticeToEventFlow y → x = y) ∧
                cauchyRateLatticeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyRateLatticeChapterTasteGate⟩,
      ⟨cauchyRateLatticeFieldFaithful⟩,
      ⟨cauchyRateLatticeNontrivial⟩,
      CauchyRateLatticeTasteGate_single_carrier_alignment_decode_encode,
      CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRateLatticeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRateLatticeUp
