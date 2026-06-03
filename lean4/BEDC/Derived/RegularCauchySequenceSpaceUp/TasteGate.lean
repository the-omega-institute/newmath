import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySequenceSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySequenceSpaceUp : Type where
  | mk (F rho sigma W D Q E H C P N : BHist) : RegularCauchySequenceSpaceUp
  deriving DecidableEq

def regularCauchySequenceSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySequenceSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySequenceSpaceEncodeBHist h

def regularCauchySequenceSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySequenceSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySequenceSpaceDecodeBHist tail)

private theorem regularCauchySequenceSpace_decode_encode_bhist :
    forall h : BHist,
      regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchySequenceSpace_mk_congr
    {F F' rho rho' sigma sigma' W W' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hF : F' = F) (hrho : rho' = rho) (hsigma : sigma' = sigma) (hW : W' = W)
    (hD : D' = D) (hQ : Q' = Q) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchySequenceSpaceUp.mk F' rho' sigma' W' D' Q' E' H' C' P' N' =
      RegularCauchySequenceSpaceUp.mk F rho sigma W D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hrho
  cases hsigma
  cases hW
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchySequenceSpaceFields : RegularCauchySequenceSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySequenceSpaceUp.mk F rho sigma W D Q E H C P N =>
      [F, rho, sigma, W, D, Q, E, H, C, P, N]

def regularCauchySequenceSpaceToEventFlow : RegularCauchySequenceSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySequenceSpaceFields x).map regularCauchySequenceSpaceEncodeBHist

private def regularCauchySequenceSpaceRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchySequenceSpaceRawAt n rest

private def regularCauchySequenceSpaceLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchySequenceSpaceLengthEq n rest

def regularCauchySequenceSpaceFromEventFlow : EventFlow -> Option RegularCauchySequenceSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchySequenceSpaceLengthEq 11 flow with
      | true =>
          some
            (RegularCauchySequenceSpaceUp.mk
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 0 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 1 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 2 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 3 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 4 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 5 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 6 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 7 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 8 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 9 flow))
              (regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceRawAt 10 flow)))
      | false => none

private theorem regularCauchySequenceSpace_round_trip :
    forall x : RegularCauchySequenceSpaceUp,
      regularCauchySequenceSpaceFromEventFlow
        (regularCauchySequenceSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F rho sigma W D Q E H C P N =>
      exact
        congrArg some
          (regularCauchySequenceSpace_mk_congr
            (regularCauchySequenceSpace_decode_encode_bhist F)
            (regularCauchySequenceSpace_decode_encode_bhist rho)
            (regularCauchySequenceSpace_decode_encode_bhist sigma)
            (regularCauchySequenceSpace_decode_encode_bhist W)
            (regularCauchySequenceSpace_decode_encode_bhist D)
            (regularCauchySequenceSpace_decode_encode_bhist Q)
            (regularCauchySequenceSpace_decode_encode_bhist E)
            (regularCauchySequenceSpace_decode_encode_bhist H)
            (regularCauchySequenceSpace_decode_encode_bhist C)
            (regularCauchySequenceSpace_decode_encode_bhist P)
            (regularCauchySequenceSpace_decode_encode_bhist N))

private theorem regularCauchySequenceSpaceToEventFlow_injective
    {x y : RegularCauchySequenceSpaceUp} :
    regularCauchySequenceSpaceToEventFlow x = regularCauchySequenceSpaceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySequenceSpaceFromEventFlow (regularCauchySequenceSpaceToEventFlow x) =
        regularCauchySequenceSpaceFromEventFlow (regularCauchySequenceSpaceToEventFlow y) :=
    congrArg regularCauchySequenceSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySequenceSpace_round_trip x).symm
      (Eq.trans hread (regularCauchySequenceSpace_round_trip y)))

instance regularCauchySequenceSpaceBHistCarrier :
    BHistCarrier RegularCauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySequenceSpaceToEventFlow
  fromEventFlow := regularCauchySequenceSpaceFromEventFlow

instance regularCauchySequenceSpaceChapterTasteGate :
    ChapterTasteGate RegularCauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySequenceSpaceFromEventFlow
      (regularCauchySequenceSpaceToEventFlow x) = some x
    exact regularCauchySequenceSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySequenceSpaceToEventFlow_injective heq)

theorem RegularCauchySequenceSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchySequenceSpaceDecodeBHist (regularCauchySequenceSpaceEncodeBHist h) = h) ∧
      (forall x : RegularCauchySequenceSpaceUp,
        regularCauchySequenceSpaceFromEventFlow
          (regularCauchySequenceSpaceToEventFlow x) = some x) ∧
        (forall x y : RegularCauchySequenceSpaceUp,
          regularCauchySequenceSpaceToEventFlow x =
              regularCauchySequenceSpaceToEventFlow y ->
            x = y) ∧
          regularCauchySequenceSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchySequenceSpace_decode_encode_bhist,
      regularCauchySequenceSpace_round_trip,
      (fun _ _ heq => regularCauchySequenceSpaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySequenceSpaceUp
