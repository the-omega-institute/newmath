import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySquareRootUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySquareRootUp : Type where
  | mk (R N W D B T M S E H C P A : BHist) : RegularCauchySquareRootUp
  deriving DecidableEq

def regularCauchySquareRootEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySquareRootEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySquareRootEncodeBHist h

def regularCauchySquareRootDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySquareRootDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySquareRootDecodeBHist tail)

private theorem regularCauchySquareRoot_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchySquareRootFields :
    RegularCauchySquareRootUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySquareRootUp.mk R N W D B T M S E H C P A =>
      [R, N, W, D, B, T, M, S, E, H, C, P, A]

def regularCauchySquareRootToEventFlow :
    RegularCauchySquareRootUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchySquareRootFields x).map
        regularCauchySquareRootEncodeBHist

private def regularCauchySquareRootEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchySquareRootEventAtDefault index rest

def regularCauchySquareRootFromEventFlow
    (ef : EventFlow) : Option RegularCauchySquareRootUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySquareRootUp.mk
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 0 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 1 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 2 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 3 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 4 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 5 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 6 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 7 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 8 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 9 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 10 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 11 ef))
      (regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEventAtDefault 12 ef)))

private theorem regularCauchySquareRoot_mk_congr
    {R R' N N' W W' D D' B B' T T' M M' S S' E E' H H' C C' P P'
      A A' : BHist}
    (hR : R' = R)
    (hN : N' = N)
    (hW : W' = W)
    (hD : D' = D)
    (hB : B' = B)
    (hT : T' = T)
    (hM : M' = M)
    (hS : S' = S)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hA : A' = A) :
    RegularCauchySquareRootUp.mk R' N' W' D' B' T' M' S' E' H' C' P' A' =
      RegularCauchySquareRootUp.mk R N W D B T M S E H C P A := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hN
  cases hW
  cases hD
  cases hB
  cases hT
  cases hM
  cases hS
  cases hE
  cases hH
  cases hC
  cases hP
  cases hA
  rfl

private theorem regularCauchySquareRoot_round_trip :
    ∀ x : RegularCauchySquareRootUp,
      regularCauchySquareRootFromEventFlow
        (regularCauchySquareRootToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R N W D B T M S E H C P A =>
      exact
        congrArg some
          (regularCauchySquareRoot_mk_congr
            (regularCauchySquareRoot_decode_encode_bhist R)
            (regularCauchySquareRoot_decode_encode_bhist N)
            (regularCauchySquareRoot_decode_encode_bhist W)
            (regularCauchySquareRoot_decode_encode_bhist D)
            (regularCauchySquareRoot_decode_encode_bhist B)
            (regularCauchySquareRoot_decode_encode_bhist T)
            (regularCauchySquareRoot_decode_encode_bhist M)
            (regularCauchySquareRoot_decode_encode_bhist S)
            (regularCauchySquareRoot_decode_encode_bhist E)
            (regularCauchySquareRoot_decode_encode_bhist H)
            (regularCauchySquareRoot_decode_encode_bhist C)
            (regularCauchySquareRoot_decode_encode_bhist P)
            (regularCauchySquareRoot_decode_encode_bhist A))

private theorem regularCauchySquareRootToEventFlow_injective
    {x y : RegularCauchySquareRootUp} :
    regularCauchySquareRootToEventFlow x =
      regularCauchySquareRootToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySquareRootFromEventFlow
          (regularCauchySquareRootToEventFlow x) =
        regularCauchySquareRootFromEventFlow
          (regularCauchySquareRootToEventFlow y) :=
    congrArg regularCauchySquareRootFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySquareRoot_round_trip x).symm
      (Eq.trans hread (regularCauchySquareRoot_round_trip y)))

instance regularCauchySquareRootBHistCarrier :
    BHistCarrier RegularCauchySquareRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySquareRootToEventFlow
  fromEventFlow := regularCauchySquareRootFromEventFlow

instance regularCauchySquareRootChapterTasteGate :
    ChapterTasteGate RegularCauchySquareRootUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySquareRootFromEventFlow
        (regularCauchySquareRootToEventFlow x) = some x
    exact regularCauchySquareRoot_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySquareRootToEventFlow_injective heq)

theorem RegularCauchySquareRootTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySquareRootDecodeBHist
        (regularCauchySquareRootEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySquareRootUp,
        regularCauchySquareRootFromEventFlow
          (regularCauchySquareRootToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySquareRootUp,
          regularCauchySquareRootToEventFlow x =
            regularCauchySquareRootToEventFlow y → x = y) ∧
          regularCauchySquareRootEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchySquareRoot_decode_encode_bhist
  · constructor
    · exact regularCauchySquareRoot_round_trip
    · constructor
      · intro x y heq
        exact regularCauchySquareRootToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchySquareRootUp
