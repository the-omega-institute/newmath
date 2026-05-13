import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryDiagonalWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryDiagonalWindowUp : Type where
  | mk :
      (q s g d r k h c p n : BHist) →
        StationaryDiagonalWindowUp
  deriving DecidableEq

private def stationaryDiagonalWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryDiagonalWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryDiagonalWindowEncodeBHist h

private def stationaryDiagonalWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryDiagonalWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryDiagonalWindowDecodeBHist tail)

private theorem stationaryDiagonalWindowDecode_encode_bhist :
    ∀ h : BHist,
      stationaryDiagonalWindowDecodeBHist
        (stationaryDiagonalWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def stationaryDiagonalWindowToEventFlow :
    StationaryDiagonalWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StationaryDiagonalWindowUp.mk q s g d r k h c p n =>
      [[BMark.b0],
        stationaryDiagonalWindowEncodeBHist q,
        [BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist g,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist k,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stationaryDiagonalWindowEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        stationaryDiagonalWindowEncodeBHist n]

private def stationaryDiagonalWindowFromEventFlow :
    EventFlow → Option StationaryDiagonalWindowUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | q :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | s :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | g :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | d :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | r :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | k :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | h :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | c :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | p :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | n ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (StationaryDiagonalWindowUp.mk
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            q)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            s)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            g)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            d)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            r)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            k)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            h)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            c)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            p)
                                                                                          (stationaryDiagonalWindowDecodeBHist
                                                                                            n))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem stationaryDiagonalWindow_round_trip :
    ∀ x : StationaryDiagonalWindowUp,
      stationaryDiagonalWindowFromEventFlow
        (stationaryDiagonalWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q s g d r k h c p n =>
      change
        some
          (StationaryDiagonalWindowUp.mk
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist q))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist s))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist g))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist d))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist r))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist k))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist h))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist c))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist p))
            (stationaryDiagonalWindowDecodeBHist (stationaryDiagonalWindowEncodeBHist n))) =
          some (StationaryDiagonalWindowUp.mk q s g d r k h c p n)
      rw [stationaryDiagonalWindowDecode_encode_bhist q,
        stationaryDiagonalWindowDecode_encode_bhist s,
        stationaryDiagonalWindowDecode_encode_bhist g,
        stationaryDiagonalWindowDecode_encode_bhist d,
        stationaryDiagonalWindowDecode_encode_bhist r,
        stationaryDiagonalWindowDecode_encode_bhist k,
        stationaryDiagonalWindowDecode_encode_bhist h,
        stationaryDiagonalWindowDecode_encode_bhist c,
        stationaryDiagonalWindowDecode_encode_bhist p,
        stationaryDiagonalWindowDecode_encode_bhist n]

private theorem stationaryDiagonalWindowToEventFlow_injective
    {x y : StationaryDiagonalWindowUp} :
    stationaryDiagonalWindowToEventFlow x =
      stationaryDiagonalWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stationaryDiagonalWindowFromEventFlow (stationaryDiagonalWindowToEventFlow x) =
        stationaryDiagonalWindowFromEventFlow (stationaryDiagonalWindowToEventFlow y) :=
    congrArg stationaryDiagonalWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stationaryDiagonalWindow_round_trip x).symm
      (Eq.trans hread (stationaryDiagonalWindow_round_trip y)))

instance stationaryDiagonalWindowBHistCarrier :
    BHistCarrier StationaryDiagonalWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryDiagonalWindowToEventFlow
  fromEventFlow := stationaryDiagonalWindowFromEventFlow

instance stationaryDiagonalWindowChapterTasteGate :
    ChapterTasteGate StationaryDiagonalWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stationaryDiagonalWindowFromEventFlow
        (stationaryDiagonalWindowToEventFlow x) = some x
    exact stationaryDiagonalWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stationaryDiagonalWindowToEventFlow_injective heq)

theorem StationaryDiagonalWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist, stationaryDiagonalWindowDecodeBHist
      (stationaryDiagonalWindowEncodeBHist h) = h) ∧
      (∀ x : StationaryDiagonalWindowUp,
        stationaryDiagonalWindowFromEventFlow
          (stationaryDiagonalWindowToEventFlow x) = some x) ∧
        (∀ x y : StationaryDiagonalWindowUp,
          stationaryDiagonalWindowToEventFlow x =
            stationaryDiagonalWindowToEventFlow y → x = y) ∧
          stationaryDiagonalWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact stationaryDiagonalWindowDecode_encode_bhist
  · constructor
    · exact stationaryDiagonalWindow_round_trip
    · constructor
      · intro x y heq
        exact stationaryDiagonalWindowToEventFlow_injective heq
      · rfl

end BEDC.Derived.StationaryDiagonalWindowUp
