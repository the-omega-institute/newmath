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

private theorem cauchyRealizer_mk_congr
    {E E' R R' V V' W W' Q Q' D D' S S' H H' C C' P P' N N' : BHist}
    (hE : E' = E) (hR : R' = R) (hV : V' = V) (hW : W' = W)
    (hQ : Q' = Q) (hD : D' = D) (hS : S' = S) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyRealizerUp.mk E' R' V' W' Q' D' S' H' C' P' N' =
      CauchyRealizerUp.mk E R V W Q D S H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hE
  cases hR
  cases hV
  cases hW
  cases hQ
  cases hD
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyRealizerFields : CauchyRealizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealizerUp.mk E R V W Q D S H C P N => [E, R, V, W, Q, D, S, H, C, P, N]

def cauchyRealizerToEventFlow : CauchyRealizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealizerFields x).map cauchyRealizerEncodeBHist

private def cauchyRealizerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyRealizerRawAt n rest

private def cauchyRealizerLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyRealizerLengthEq n rest

def cauchyRealizerFromEventFlow : EventFlow → Option CauchyRealizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyRealizerLengthEq 11 flow with
      | true =>
          some
            (CauchyRealizerUp.mk
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 0 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 1 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 2 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 3 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 4 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 5 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 6 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 7 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 8 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 9 flow))
              (cauchyRealizerDecodeBHist (cauchyRealizerRawAt 10 flow)))
      | false => none

private theorem cauchyRealizer_round_trip :
    ∀ x : CauchyRealizerUp,
      cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E R V W Q D S H C P N =>
      exact
        congrArg some
          (cauchyRealizer_mk_congr
            (cauchyRealizer_decode_encode_bhist E)
            (cauchyRealizer_decode_encode_bhist R)
            (cauchyRealizer_decode_encode_bhist V)
            (cauchyRealizer_decode_encode_bhist W)
            (cauchyRealizer_decode_encode_bhist Q)
            (cauchyRealizer_decode_encode_bhist D)
            (cauchyRealizer_decode_encode_bhist S)
            (cauchyRealizer_decode_encode_bhist H)
            (cauchyRealizer_decode_encode_bhist C)
            (cauchyRealizer_decode_encode_bhist P)
            (cauchyRealizer_decode_encode_bhist N))

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

theorem CauchyRealizerUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealizerDecodeBHist (cauchyRealizerEncodeBHist h) = h) ∧
      (∀ x : CauchyRealizerUp,
        cauchyRealizerFromEventFlow (cauchyRealizerToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealizerUp,
          cauchyRealizerToEventFlow x = cauchyRealizerToEventFlow y → x = y) ∧
          cauchyRealizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyRealizer_decode_encode_bhist,
      cauchyRealizer_round_trip,
      (fun _ _ heq => cauchyRealizerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRealizerUp
