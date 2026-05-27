import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyInterleavingProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyInterleavingProductUp : Type where
  | mk (A B SA SB sigma M DA DB D E R I H C P N : BHist) :
      CauchyInterleavingProductUp
  deriving DecidableEq

def cauchyInterleavingProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyInterleavingProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyInterleavingProductEncodeBHist h

def cauchyInterleavingProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyInterleavingProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyInterleavingProductDecodeBHist tail)

private theorem cauchyInterleavingProduct_decode_encode_bhist :
    ∀ h : BHist,
      cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyInterleavingProductFields : CauchyInterleavingProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyInterleavingProductUp.mk A B SA SB sigma M DA DB D E R I H C P N =>
      [A, B, SA, SB, sigma, M, DA, DB, D, E, R, I, H, C, P, N]

def cauchyInterleavingProductToEventFlow : CauchyInterleavingProductUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyInterleavingProductFields x).map cauchyInterleavingProductEncodeBHist

private def cauchyInterleavingProductEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyInterleavingProductEventAtDefault index rest

def cauchyInterleavingProductFromEventFlow : EventFlow → Option CauchyInterleavingProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyInterleavingProductUp.mk
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 0 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 1 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 2 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 3 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 4 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 5 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 6 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 7 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 8 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 9 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 10 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 11 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 12 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 13 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 14 ef))
        (cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEventAtDefault 15 ef)))

private theorem cauchyInterleavingProduct_round_trip :
    ∀ x : CauchyInterleavingProductUp,
      cauchyInterleavingProductFromEventFlow (cauchyInterleavingProductToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B SA SB sigma M DA DB D E R I H C P N =>
      change
        some
          (CauchyInterleavingProductUp.mk
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist A))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist B))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist SA))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist SB))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist sigma))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist M))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist DA))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist DB))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist D))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist E))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist R))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist I))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist H))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist C))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist P))
            (cauchyInterleavingProductDecodeBHist
              (cauchyInterleavingProductEncodeBHist N))) =
          some (CauchyInterleavingProductUp.mk A B SA SB sigma M DA DB D E R I H C P N)
      rw [cauchyInterleavingProduct_decode_encode_bhist A,
        cauchyInterleavingProduct_decode_encode_bhist B,
        cauchyInterleavingProduct_decode_encode_bhist SA,
        cauchyInterleavingProduct_decode_encode_bhist SB,
        cauchyInterleavingProduct_decode_encode_bhist sigma,
        cauchyInterleavingProduct_decode_encode_bhist M,
        cauchyInterleavingProduct_decode_encode_bhist DA,
        cauchyInterleavingProduct_decode_encode_bhist DB,
        cauchyInterleavingProduct_decode_encode_bhist D,
        cauchyInterleavingProduct_decode_encode_bhist E,
        cauchyInterleavingProduct_decode_encode_bhist R,
        cauchyInterleavingProduct_decode_encode_bhist I,
        cauchyInterleavingProduct_decode_encode_bhist H,
        cauchyInterleavingProduct_decode_encode_bhist C,
        cauchyInterleavingProduct_decode_encode_bhist P,
        cauchyInterleavingProduct_decode_encode_bhist N]

private theorem cauchyInterleavingProductToEventFlow_injective
    {x y : CauchyInterleavingProductUp} :
    cauchyInterleavingProductToEventFlow x = cauchyInterleavingProductToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyInterleavingProductFromEventFlow (cauchyInterleavingProductToEventFlow x) =
        cauchyInterleavingProductFromEventFlow (cauchyInterleavingProductToEventFlow y) :=
    congrArg cauchyInterleavingProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyInterleavingProduct_round_trip x).symm
      (Eq.trans hread (cauchyInterleavingProduct_round_trip y)))

instance cauchyInterleavingProductBHistCarrier : BHistCarrier CauchyInterleavingProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyInterleavingProductToEventFlow
  fromEventFlow := cauchyInterleavingProductFromEventFlow

instance cauchyInterleavingProductChapterTasteGate :
    ChapterTasteGate CauchyInterleavingProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyInterleavingProductFromEventFlow (cauchyInterleavingProductToEventFlow x) =
        some x
    exact cauchyInterleavingProduct_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyInterleavingProductToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyInterleavingProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyInterleavingProductChapterTasteGate

theorem CauchyInterleavingProductTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyInterleavingProductDecodeBHist (cauchyInterleavingProductEncodeBHist h) = h) ∧
      (∀ x : CauchyInterleavingProductUp,
        cauchyInterleavingProductFromEventFlow (cauchyInterleavingProductToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyInterleavingProductUp,
          cauchyInterleavingProductToEventFlow x = cauchyInterleavingProductToEventFlow y →
            x = y) ∧
          cauchyInterleavingProductEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyInterleavingProduct_decode_encode_bhist,
      cauchyInterleavingProduct_round_trip,
      (fun _ _ heq => cauchyInterleavingProductToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyInterleavingProductUp
