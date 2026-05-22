import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySchwarzRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySchwarzRealUp : Type where
  | mk :
      (vectorSource vectorLeft vectorRight innerProduct normSquareLeft normSquareRight
        dyadicLedger readback streamWindow realSeal transport replay provenance localCert : BHist) →
      CauchySchwarzRealUp
  deriving DecidableEq

def cauchySchwarzRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySchwarzRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySchwarzRealEncodeBHist h

def cauchySchwarzRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySchwarzRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySchwarzRealDecodeBHist tail)

private theorem cauchySchwarzRealDecode_encode_bhist :
    ∀ h : BHist, cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySchwarzRealFields : CauchySchwarzRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySchwarzRealUp.mk vectorSource vectorLeft vectorRight innerProduct normSquareLeft
      normSquareRight dyadicLedger readback streamWindow realSeal transport replay provenance
      localCert =>
      [vectorSource, vectorLeft, vectorRight, innerProduct, normSquareLeft, normSquareRight,
        dyadicLedger, readback, streamWindow, realSeal, transport, replay, provenance, localCert]

def cauchySchwarzRealToEventFlow : CauchySchwarzRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchySchwarzRealEncodeBHist (cauchySchwarzRealFields x)

private def cauchySchwarzRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySchwarzRealEventAtDefault index rest

def cauchySchwarzRealFromEventFlow : EventFlow → Option CauchySchwarzRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchySchwarzRealUp.mk
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 0 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 1 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 2 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 3 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 4 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 5 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 6 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 7 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 8 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 9 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 10 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 11 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 12 ef))
        (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAtDefault 13 ef)))

private theorem cauchySchwarzReal_round_trip :
    ∀ x : CauchySchwarzRealUp,
      cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk vectorSource vectorLeft vectorRight innerProduct normSquareLeft normSquareRight
      dyadicLedger readback streamWindow realSeal transport replay provenance localCert =>
      change
        some
          (CauchySchwarzRealUp.mk
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist vectorSource))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist vectorLeft))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist vectorRight))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist innerProduct))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist normSquareLeft))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist normSquareRight))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist dyadicLedger))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist readback))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist streamWindow))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist realSeal))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist transport))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist replay))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist provenance))
            (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist localCert))) =
          some
            (CauchySchwarzRealUp.mk vectorSource vectorLeft vectorRight innerProduct
              normSquareLeft normSquareRight dyadicLedger readback streamWindow realSeal
              transport replay provenance localCert)
      rw [cauchySchwarzRealDecode_encode_bhist vectorSource,
        cauchySchwarzRealDecode_encode_bhist vectorLeft,
        cauchySchwarzRealDecode_encode_bhist vectorRight,
        cauchySchwarzRealDecode_encode_bhist innerProduct,
        cauchySchwarzRealDecode_encode_bhist normSquareLeft,
        cauchySchwarzRealDecode_encode_bhist normSquareRight,
        cauchySchwarzRealDecode_encode_bhist dyadicLedger,
        cauchySchwarzRealDecode_encode_bhist readback,
        cauchySchwarzRealDecode_encode_bhist streamWindow,
        cauchySchwarzRealDecode_encode_bhist realSeal,
        cauchySchwarzRealDecode_encode_bhist transport,
        cauchySchwarzRealDecode_encode_bhist replay,
        cauchySchwarzRealDecode_encode_bhist provenance,
        cauchySchwarzRealDecode_encode_bhist localCert]

private theorem cauchySchwarzRealToEventFlow_injective {x y : CauchySchwarzRealUp} :
    cauchySchwarzRealToEventFlow x = cauchySchwarzRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) =
        cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow y) :=
    congrArg cauchySchwarzRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySchwarzReal_round_trip x).symm
      (Eq.trans hread (cauchySchwarzReal_round_trip y)))

instance cauchySchwarzRealBHistCarrier : BHistCarrier CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySchwarzRealToEventFlow
  fromEventFlow := cauchySchwarzRealFromEventFlow

instance cauchySchwarzRealChapterTasteGate : ChapterTasteGate CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x
    exact cauchySchwarzReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySchwarzRealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySchwarzRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySchwarzRealChapterTasteGate

theorem CauchySchwarzRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist h) = h) ∧
      (∀ x : CauchySchwarzRealUp,
        cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x) ∧
      (∀ x y : CauchySchwarzRealUp,
        cauchySchwarzRealToEventFlow x = cauchySchwarzRealToEventFlow y → x = y) ∧
      Nonempty (ChapterTasteGate CauchySchwarzRealUp) ∧
      cauchySchwarzRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact cauchySchwarzRealDecode_encode_bhist
  · constructor
    · exact cauchySchwarzReal_round_trip
    · constructor
      · intro x y heq
        exact cauchySchwarzRealToEventFlow_injective heq
      · constructor
        · exact ⟨cauchySchwarzRealChapterTasteGate⟩
        · rfl

end BEDC.Derived.CauchySchwarzRealUp.TasteGate
