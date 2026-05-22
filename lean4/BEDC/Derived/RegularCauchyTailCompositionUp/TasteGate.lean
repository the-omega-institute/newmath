import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailCompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailCompositionUp : Type where
  | mk (T1 T2 B W D R E H C P N : BHist) : RegularCauchyTailCompositionUp
  deriving DecidableEq

def regularCauchyTailCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailCompositionEncodeBHist h

def regularCauchyTailCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailCompositionDecodeBHist tail)

private theorem regularCauchyTailComposition_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailCompositionFields :
    RegularCauchyTailCompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailCompositionUp.mk T1 T2 B W D R E H C P N =>
      [T1, T2, B, W, D, R, E, H, C, P, N]

def regularCauchyTailCompositionToEventFlow :
    RegularCauchyTailCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyTailCompositionFields x).map
        regularCauchyTailCompositionEncodeBHist

private def regularCauchyTailCompositionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyTailCompositionEventAtDefault index rest

def regularCauchyTailCompositionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTailCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailCompositionUp.mk
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 0 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 1 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 2 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 3 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 4 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 5 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 6 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 7 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 8 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 9 ef))
      (regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEventAtDefault 10 ef)))

private theorem regularCauchyTailComposition_mk_congr
    {T1 T1' T2 T2' B B' W W' D D' R R' E E' H H' C C' P P' N N' : BHist}
    (hT1 : T1' = T1)
    (hT2 : T2' = T2)
    (hB : B' = B)
    (hW : W' = W)
    (hD : D' = D)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RegularCauchyTailCompositionUp.mk T1' T2' B' W' D' R' E' H' C' P' N' =
      RegularCauchyTailCompositionUp.mk T1 T2 B W D R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT1
  cases hT2
  cases hB
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem regularCauchyTailComposition_round_trip :
    ∀ x : RegularCauchyTailCompositionUp,
      regularCauchyTailCompositionFromEventFlow
        (regularCauchyTailCompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T1 T2 B W D R E H C P N =>
      exact
        congrArg some
          (regularCauchyTailComposition_mk_congr
            (regularCauchyTailComposition_decode_encode_bhist T1)
            (regularCauchyTailComposition_decode_encode_bhist T2)
            (regularCauchyTailComposition_decode_encode_bhist B)
            (regularCauchyTailComposition_decode_encode_bhist W)
            (regularCauchyTailComposition_decode_encode_bhist D)
            (regularCauchyTailComposition_decode_encode_bhist R)
            (regularCauchyTailComposition_decode_encode_bhist E)
            (regularCauchyTailComposition_decode_encode_bhist H)
            (regularCauchyTailComposition_decode_encode_bhist C)
            (regularCauchyTailComposition_decode_encode_bhist P)
            (regularCauchyTailComposition_decode_encode_bhist N))

private theorem regularCauchyTailCompositionToEventFlow_injective
    {x y : RegularCauchyTailCompositionUp} :
    regularCauchyTailCompositionToEventFlow x =
      regularCauchyTailCompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailCompositionFromEventFlow
          (regularCauchyTailCompositionToEventFlow x) =
        regularCauchyTailCompositionFromEventFlow
          (regularCauchyTailCompositionToEventFlow y) :=
    congrArg regularCauchyTailCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailComposition_round_trip x).symm
      (Eq.trans hread (regularCauchyTailComposition_round_trip y)))

instance regularCauchyTailCompositionBHistCarrier :
    BHistCarrier RegularCauchyTailCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailCompositionToEventFlow
  fromEventFlow := regularCauchyTailCompositionFromEventFlow

instance regularCauchyTailCompositionChapterTasteGate :
    ChapterTasteGate RegularCauchyTailCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailCompositionFromEventFlow
        (regularCauchyTailCompositionToEventFlow x) = some x
    exact regularCauchyTailComposition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailCompositionToEventFlow_injective heq)

theorem RegularCauchyTailCompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailCompositionDecodeBHist
        (regularCauchyTailCompositionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailCompositionUp,
        regularCauchyTailCompositionFromEventFlow
          (regularCauchyTailCompositionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailCompositionUp,
          regularCauchyTailCompositionToEventFlow x =
            regularCauchyTailCompositionToEventFlow y → x = y) ∧
          regularCauchyTailCompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyTailComposition_decode_encode_bhist
  · constructor
    · exact regularCauchyTailComposition_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTailCompositionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyTailCompositionUp
