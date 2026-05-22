import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealizerUp : Type where
  | mk (E R V W Q D S H C P N : BHist) : CauchyRealizerUp
  deriving DecidableEq

def cauchyRealizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealizerEncodeBHist h

def cauchyRealizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealizerDecodeBHist tail)

private theorem cauchyRealizer_decode_encode_bhist :
    ∀ h : BHist, cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealizerFields : CauchyRealizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealizerUp.mk E R V W Q D S H C P N => [E, R, V, W, Q, D, S, H, C, P, N]

def cauchyRealizerToEventFlow : CauchyRealizerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyRealizerFields x).map cauchyRealizerEncodeBHist

private def cauchyRealizerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealizerEventAtDefault index rest

def cauchyRealizerFromEventFlow (ef : EventFlow) : Option CauchyRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealizerUp.mk
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 0 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 1 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 2 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 3 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 4 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 5 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 6 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 7 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 8 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 9 ef))
      (cauchyRealizerDecodeBHist (cauchyRealizerEventAtDefault 10 ef)))

private theorem cauchyRealizer_round_trip :
    ∀ x : CauchyRealizerUp,
      cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E R V W Q D S H C P N =>
      change
        some
          (CauchyRealizerUp.mk
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist E))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist R))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist V))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist W))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist Q))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist D))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist S))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist H))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist C))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist P))
            (cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist N))) =
          some (CauchyRealizerUp.mk E R V W Q D S H C P N)
      rw [cauchyRealizer_decode_encode_bhist E,
        cauchyRealizer_decode_encode_bhist R,
        cauchyRealizer_decode_encode_bhist V,
        cauchyRealizer_decode_encode_bhist W,
        cauchyRealizer_decode_encode_bhist Q,
        cauchyRealizer_decode_encode_bhist D,
        cauchyRealizer_decode_encode_bhist S,
        cauchyRealizer_decode_encode_bhist H,
        cauchyRealizer_decode_encode_bhist C,
        cauchyRealizer_decode_encode_bhist P,
        cauchyRealizer_decode_encode_bhist N]

private theorem cauchyRealizerToEventFlow_injective {x y : CauchyRealizerUp} :
    cauchyRealizerToEventFlow x = cauchyRealizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow x) =
        cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow y) :=
    congrArg cauchyRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRealizer_round_trip x).symm
      (Eq.trans hread (cauchyRealizer_round_trip y)))

instance cauchyRealizerBHistCarrier : BHistCarrier CauchyRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealizerToEventFlow
  fromEventFlow := cauchyRealizerFromEventFlow

instance cauchyRealizerChapterTasteGate : ChapterTasteGate CauchyRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow x) = some x
    exact cauchyRealizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRealizerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealizerChapterTasteGate

theorem CauchyRealizerTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist h) = h) ∧
      (∀ x : CauchyRealizerUp,
        cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow x) = some x) ∧
      (∀ x y : CauchyRealizerUp,
        cauchyRealizerToEventFlow x = cauchyRealizerToEventFlow y → x = y) ∧
      cauchyRealizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyRealizer_decode_encode_bhist,
      cauchyRealizer_round_trip,
      (fun _ _ heq => cauchyRealizerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRealizerUp
