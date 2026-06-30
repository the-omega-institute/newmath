import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyPowerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyPowerUp : Type where
  | mk (n A W D S R E H C P N : BHist) : RegularCauchyPowerUp

def regularCauchyPowerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyPowerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyPowerEncodeBHist h

def regularCauchyPowerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyPowerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyPowerDecodeBHist tail)

theorem RegularCauchyPowerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyPowerToEventFlow : RegularCauchyPowerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyPowerUp.mk n A W D S R E H C P N =>
      [[BMark.b0],
        regularCauchyPowerEncodeBHist n,
        [BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyPowerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyPowerEncodeBHist N]

def regularCauchyPowerFromEventFlow : EventFlow → Option RegularCauchyPowerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | n :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | S :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RegularCauchyPowerUp.mk
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    n)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    A)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    W)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    D)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    S)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    R)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    E)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    H)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    C)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    P)
                                                                                                  (regularCauchyPowerDecodeBHist
                                                                                                    N))
                                                                                          | _ :: _ =>
                                                                                              none

theorem RegularCauchyPowerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyPowerUp,
      regularCauchyPowerFromEventFlow (regularCauchyPowerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk n A W D S R E H C P N =>
      change
        some
          (RegularCauchyPowerUp.mk
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist n))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist A))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist W))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist D))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist S))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist R))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist E))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist H))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist C))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist P))
            (regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist N))) =
          some (RegularCauchyPowerUp.mk n A W D S R E H C P N)
      rw [RegularCauchyPowerTasteGate_single_carrier_alignment_decode n,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode A,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode W,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode D,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode S,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode R,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode E,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode H,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode C,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode P,
        RegularCauchyPowerTasteGate_single_carrier_alignment_decode N]

theorem RegularCauchyPowerTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyPowerUp} :
    regularCauchyPowerToEventFlow x = regularCauchyPowerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyPowerFromEventFlow (regularCauchyPowerToEventFlow x) =
        regularCauchyPowerFromEventFlow (regularCauchyPowerToEventFlow y) :=
    congrArg regularCauchyPowerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyPowerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyPowerTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyPowerBHistCarrier : BHistCarrier RegularCauchyPowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyPowerToEventFlow
  fromEventFlow := regularCauchyPowerFromEventFlow

instance regularCauchyPowerChapterTasteGate : ChapterTasteGate RegularCauchyPowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyPowerFromEventFlow (regularCauchyPowerToEventFlow x) = some x
    exact RegularCauchyPowerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyPowerTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyPowerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyPowerChapterTasteGate

theorem RegularCauchyPowerTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyPowerDecodeBHist (regularCauchyPowerEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyPowerUp,
        regularCauchyPowerFromEventFlow (regularCauchyPowerToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyPowerUp,
          regularCauchyPowerToEventFlow x = regularCauchyPowerToEventFlow y → x = y) ∧
          regularCauchyPowerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyPowerTasteGate_single_carrier_alignment_decode,
      RegularCauchyPowerTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => RegularCauchyPowerTasteGate_single_carrier_alignment_injective heq, rfl⟩

end BEDC.Derived.RegularCauchyPowerUp
