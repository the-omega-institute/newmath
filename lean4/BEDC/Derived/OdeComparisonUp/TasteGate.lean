import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OdeComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OdeComparisonUp : Type where
  | mk (D0 D1 I L M G S R E H C P N : BHist) : OdeComparisonUp
  deriving DecidableEq

def odeComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: odeComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: odeComparisonEncodeBHist h

def odeComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (odeComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (odeComparisonDecodeBHist tail)

private theorem odeComparisonDecode_encode_bhist :
    ∀ h : BHist, odeComparisonDecodeBHist (odeComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def odeComparisonFields : OdeComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OdeComparisonUp.mk D0 D1 I L M G S R E H C P N =>
      [D0, D1, I, L, M, G, S, R, E, H, C, P, N]

def odeComparisonToEventFlow : OdeComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (odeComparisonFields x).map odeComparisonEncodeBHist

private def odeComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => odeComparisonEventAtDefault index rest

def odeComparisonFromEventFlow (ef : EventFlow) : Option OdeComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OdeComparisonUp.mk
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 0 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 1 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 2 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 3 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 4 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 5 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 6 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 7 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 8 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 9 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 10 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 11 ef))
      (odeComparisonDecodeBHist (odeComparisonEventAtDefault 12 ef)))

private theorem odeComparison_round_trip :
    ∀ x : OdeComparisonUp,
      odeComparisonFromEventFlow (odeComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D0 D1 I L M G S R E H C P N =>
      change
        some
          (OdeComparisonUp.mk
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist D0))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist D1))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist I))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist L))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist M))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist G))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist S))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist R))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist E))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist H))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist C))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist P))
            (odeComparisonDecodeBHist (odeComparisonEncodeBHist N))) =
          some (OdeComparisonUp.mk D0 D1 I L M G S R E H C P N)
      rw [odeComparisonDecode_encode_bhist D0, odeComparisonDecode_encode_bhist D1,
        odeComparisonDecode_encode_bhist I, odeComparisonDecode_encode_bhist L,
        odeComparisonDecode_encode_bhist M, odeComparisonDecode_encode_bhist G,
        odeComparisonDecode_encode_bhist S, odeComparisonDecode_encode_bhist R,
        odeComparisonDecode_encode_bhist E, odeComparisonDecode_encode_bhist H,
        odeComparisonDecode_encode_bhist C, odeComparisonDecode_encode_bhist P,
        odeComparisonDecode_encode_bhist N]

private theorem odeComparisonToEventFlow_injective {x y : OdeComparisonUp} :
    odeComparisonToEventFlow x = odeComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      odeComparisonFromEventFlow (odeComparisonToEventFlow x) =
        odeComparisonFromEventFlow (odeComparisonToEventFlow y) :=
    congrArg odeComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (odeComparison_round_trip x).symm
      (Eq.trans hread (odeComparison_round_trip y)))

instance odeComparisonBHistCarrier : BHistCarrier OdeComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := odeComparisonToEventFlow
  fromEventFlow := odeComparisonFromEventFlow

instance odeComparisonChapterTasteGate : ChapterTasteGate OdeComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change odeComparisonFromEventFlow (odeComparisonToEventFlow x) = some x
    exact odeComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (odeComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate OdeComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  odeComparisonChapterTasteGate

theorem OdeComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist, odeComparisonDecodeBHist (odeComparisonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier OdeComparisonUp) ∧
        Nonempty (ChapterTasteGate OdeComparisonUp) ∧
          odeComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨odeComparisonDecode_encode_bhist,
      ⟨odeComparisonBHistCarrier⟩,
      ⟨odeComparisonChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.OdeComparisonUp
