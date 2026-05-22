import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchyModulusUp : Type where
  | mk (M F S D Q E H C P N : BHist) : FastCauchyModulusUp
  deriving DecidableEq

def fastCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchyModulusEncodeBHist h

def fastCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchyModulusDecodeBHist tail)

private theorem fastCauchyModulus_decode_encode_bhist :
    ∀ h : BHist, fastCauchyModulusDecodeBHist (fastCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem fastCauchyModulus_mk_congr
    {M M' F F' S S' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hF : F' = F) (hS : S' = S) (hD : D' = D)
    (hQ : Q' = Q) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    FastCauchyModulusUp.mk M' F' S' D' Q' E' H' C' P' N' =
      FastCauchyModulusUp.mk M F S D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hF
  cases hS
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def fastCauchyModulusFields : FastCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchyModulusUp.mk M F S D Q E H C P N => [M, F, S, D, Q, E, H, C, P, N]

def fastCauchyModulusToEventFlow : FastCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fastCauchyModulusFields x).map fastCauchyModulusEncodeBHist

private def fastCauchyModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fastCauchyModulusRawAt n rest

private def fastCauchyModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => fastCauchyModulusLengthEq n rest

def fastCauchyModulusFromEventFlow : EventFlow → Option FastCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match fastCauchyModulusLengthEq 10 flow with
      | true =>
          some
            (FastCauchyModulusUp.mk
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 0 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 1 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 2 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 3 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 4 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 5 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 6 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 7 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 8 flow))
              (fastCauchyModulusDecodeBHist (fastCauchyModulusRawAt 9 flow)))
      | false => none

private theorem fastCauchyModulus_round_trip :
    ∀ x : FastCauchyModulusUp,
      fastCauchyModulusFromEventFlow (fastCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F S D Q E H C P N =>
      exact
        congrArg some
          (fastCauchyModulus_mk_congr
            (fastCauchyModulus_decode_encode_bhist M)
            (fastCauchyModulus_decode_encode_bhist F)
            (fastCauchyModulus_decode_encode_bhist S)
            (fastCauchyModulus_decode_encode_bhist D)
            (fastCauchyModulus_decode_encode_bhist Q)
            (fastCauchyModulus_decode_encode_bhist E)
            (fastCauchyModulus_decode_encode_bhist H)
            (fastCauchyModulus_decode_encode_bhist C)
            (fastCauchyModulus_decode_encode_bhist P)
            (fastCauchyModulus_decode_encode_bhist N))

private theorem fastCauchyModulusToEventFlow_injective {x y : FastCauchyModulusUp} :
    fastCauchyModulusToEventFlow x = fastCauchyModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchyModulusFromEventFlow (fastCauchyModulusToEventFlow x) =
        fastCauchyModulusFromEventFlow (fastCauchyModulusToEventFlow y) :=
    congrArg fastCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastCauchyModulus_round_trip x).symm
      (Eq.trans hread (fastCauchyModulus_round_trip y)))

instance fastCauchyModulusBHistCarrier : BHistCarrier FastCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchyModulusToEventFlow
  fromEventFlow := fastCauchyModulusFromEventFlow

instance fastCauchyModulusChapterTasteGate : ChapterTasteGate FastCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchyModulusFromEventFlow (fastCauchyModulusToEventFlow x) = some x
    exact fastCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastCauchyModulusToEventFlow_injective heq)

theorem FastCauchyModulusUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, fastCauchyModulusDecodeBHist (fastCauchyModulusEncodeBHist h) = h) ∧
      (∀ x : FastCauchyModulusUp,
        fastCauchyModulusFromEventFlow (fastCauchyModulusToEventFlow x) = some x) ∧
        (∀ x y : FastCauchyModulusUp,
          fastCauchyModulusToEventFlow x = fastCauchyModulusToEventFlow y → x = y) ∧
          fastCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨fastCauchyModulus_decode_encode_bhist,
      fastCauchyModulus_round_trip,
      (fun _ _ heq => fastCauchyModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FastCauchyModulusUp
