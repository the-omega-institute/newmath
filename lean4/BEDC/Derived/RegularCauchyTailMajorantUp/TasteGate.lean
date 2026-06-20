import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailMajorantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailMajorantUp : Type where
  | mk (S M D R E H C P N : BHist) : RegularCauchyTailMajorantUp
  deriving DecidableEq

def regularCauchyTailMajorantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailMajorantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailMajorantEncodeBHist h

def regularCauchyTailMajorantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailMajorantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailMajorantDecodeBHist tail)

private theorem regularCauchyTailMajorant_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailMajorantDecodeBHist
        (regularCauchyTailMajorantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailMajorantToEventFlow :
    RegularCauchyTailMajorantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailMajorantUp.mk S M D R E H C P N =>
      [regularCauchyTailMajorantEncodeBHist S,
        regularCauchyTailMajorantEncodeBHist M,
        regularCauchyTailMajorantEncodeBHist D,
        regularCauchyTailMajorantEncodeBHist R,
        regularCauchyTailMajorantEncodeBHist E,
        regularCauchyTailMajorantEncodeBHist H,
        regularCauchyTailMajorantEncodeBHist C,
        regularCauchyTailMajorantEncodeBHist P,
        regularCauchyTailMajorantEncodeBHist N]

def regularCauchyTailMajorantFromEventFlow :
    EventFlow → Option RegularCauchyTailMajorantUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RegularCauchyTailMajorantUp.mk
                                              (regularCauchyTailMajorantDecodeBHist S)
                                              (regularCauchyTailMajorantDecodeBHist M)
                                              (regularCauchyTailMajorantDecodeBHist D)
                                              (regularCauchyTailMajorantDecodeBHist R)
                                              (regularCauchyTailMajorantDecodeBHist E)
                                              (regularCauchyTailMajorantDecodeBHist H)
                                              (regularCauchyTailMajorantDecodeBHist C)
                                              (regularCauchyTailMajorantDecodeBHist P)
                                              (regularCauchyTailMajorantDecodeBHist N))
                                      | _ :: _ => none

private theorem regularCauchyTailMajorant_round_trip :
    ∀ x : RegularCauchyTailMajorantUp,
      regularCauchyTailMajorantFromEventFlow
        (regularCauchyTailMajorantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D R E H C P N =>
      change
        some
          (RegularCauchyTailMajorantUp.mk
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist S))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist M))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist D))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist R))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist E))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist H))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist C))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist P))
            (regularCauchyTailMajorantDecodeBHist
              (regularCauchyTailMajorantEncodeBHist N))) =
          some (RegularCauchyTailMajorantUp.mk S M D R E H C P N)
      rw [regularCauchyTailMajorant_decode_encode_bhist S,
        regularCauchyTailMajorant_decode_encode_bhist M,
        regularCauchyTailMajorant_decode_encode_bhist D,
        regularCauchyTailMajorant_decode_encode_bhist R,
        regularCauchyTailMajorant_decode_encode_bhist E,
        regularCauchyTailMajorant_decode_encode_bhist H,
        regularCauchyTailMajorant_decode_encode_bhist C,
        regularCauchyTailMajorant_decode_encode_bhist P,
        regularCauchyTailMajorant_decode_encode_bhist N]

private theorem regularCauchyTailMajorantToEventFlow_injective
    {x y : RegularCauchyTailMajorantUp} :
    regularCauchyTailMajorantToEventFlow x =
        regularCauchyTailMajorantToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailMajorantFromEventFlow
          (regularCauchyTailMajorantToEventFlow x) =
        regularCauchyTailMajorantFromEventFlow
          (regularCauchyTailMajorantToEventFlow y) :=
    congrArg regularCauchyTailMajorantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailMajorant_round_trip x).symm
      (Eq.trans hread (regularCauchyTailMajorant_round_trip y)))

instance regularCauchyTailMajorantBHistCarrier :
    BHistCarrier RegularCauchyTailMajorantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailMajorantToEventFlow
  fromEventFlow := regularCauchyTailMajorantFromEventFlow

instance regularCauchyTailMajorantChapterTasteGate :
    ChapterTasteGate RegularCauchyTailMajorantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailMajorantFromEventFlow
        (regularCauchyTailMajorantToEventFlow x) = some x
    exact regularCauchyTailMajorant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailMajorantToEventFlow_injective heq)

theorem RegularCauchyTailMajorantTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyTailMajorantDecodeBHist
          (regularCauchyTailMajorantEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailMajorantUp,
        regularCauchyTailMajorantFromEventFlow
          (regularCauchyTailMajorantToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailMajorantUp,
          regularCauchyTailMajorantToEventFlow x =
              regularCauchyTailMajorantToEventFlow y →
            x = y) ∧
          regularCauchyTailMajorantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyTailMajorant_decode_encode_bhist,
      regularCauchyTailMajorant_round_trip,
      (fun _x _y heq => regularCauchyTailMajorantToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyTailMajorantUp
