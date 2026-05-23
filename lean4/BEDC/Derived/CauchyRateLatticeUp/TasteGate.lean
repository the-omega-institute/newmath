import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
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

private theorem CauchyRateLatticeTasteGate_single_carrier_alignment_decode :
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
  | x => List.map cauchyRateLatticeEncodeBHist (cauchyRateLatticeFields x)

private def cauchyRateLatticeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRateLatticeRawAt index rest

def cauchyRateLatticeFromEventFlow : EventFlow → Option CauchyRateLatticeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (CauchyRateLatticeUp.mk
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 0 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 1 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 2 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 3 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 4 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 5 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 6 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 7 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 8 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 9 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 10 flow))
          (cauchyRateLatticeDecodeBHist (cauchyRateLatticeRawAt 11 flow)))

private theorem CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRateLatticeUp,
      cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
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
      rw [CauchyRateLatticeTasteGate_single_carrier_alignment_decode A,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode B,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode M,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode J,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode D,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode S,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode R,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode E,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode H,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode C,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode P,
        CauchyRateLatticeTasteGate_single_carrier_alignment_decode N]

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
      (Eq.trans hread (CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyRateLattice_field_faithful :
    ∀ x y : CauchyRateLatticeUp, cauchyRateLatticeFields x = cauchyRateLatticeFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
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
  field_faithful := cauchyRateLattice_field_faithful

instance cauchyRateLatticeNontrivial : Nontrivial CauchyRateLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRateLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRateLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRateLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateLatticeChapterTasteGate

theorem CauchyRateLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRateLatticeDecodeBHist (cauchyRateLatticeEncodeBHist h) = h) ∧
      (∀ x : CauchyRateLatticeUp,
        cauchyRateLatticeFromEventFlow (cauchyRateLatticeToEventFlow x) = some x) ∧
        (∀ x y : CauchyRateLatticeUp,
          cauchyRateLatticeToEventFlow x = cauchyRateLatticeToEventFlow y → x = y) ∧
          cauchyRateLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CauchyRateLatticeTasteGate_single_carrier_alignment_decode,
      CauchyRateLatticeTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact CauchyRateLatticeTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyRateLatticeUp
