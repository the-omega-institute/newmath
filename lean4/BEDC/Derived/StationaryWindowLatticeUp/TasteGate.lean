import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryWindowLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryWindowLatticeUp : Type where
  | mk :
      (q s r d w m h c p n : BHist) →
        StationaryWindowLatticeUp
  deriving DecidableEq

def stationaryWindowLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryWindowLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryWindowLatticeEncodeBHist h

def stationaryWindowLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryWindowLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryWindowLatticeDecodeBHist tail)

private theorem stationaryWindowLatticeDecode_encode_bhist :
    ∀ h : BHist,
      stationaryWindowLatticeDecodeBHist
        (stationaryWindowLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stationaryWindowLatticeToEventFlow :
    StationaryWindowLatticeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StationaryWindowLatticeUp.mk q s r d w m h c p n =>
      [[BMark.b0],
        stationaryWindowLatticeEncodeBHist q,
        [BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist m,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stationaryWindowLatticeEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowLatticeEncodeBHist n]

def stationaryWindowLatticeFromEventFlow :
    EventFlow → Option StationaryWindowLatticeUp
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
                      | r :: rest5 =>
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
                                      | w :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | m :: rest11 =>
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
                                                                                        (StationaryWindowLatticeUp.mk
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            q)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            s)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            r)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            d)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            w)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            m)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            h)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            c)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            p)
                                                                                          (stationaryWindowLatticeDecodeBHist
                                                                                            n))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem stationaryWindowLattice_round_trip :
    ∀ x : StationaryWindowLatticeUp,
      stationaryWindowLatticeFromEventFlow
        (stationaryWindowLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q s r d w m h c p n =>
      change
        some
          (StationaryWindowLatticeUp.mk
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist q))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist s))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist r))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist d))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist w))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist m))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist h))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist c))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist p))
            (stationaryWindowLatticeDecodeBHist (stationaryWindowLatticeEncodeBHist n))) =
          some (StationaryWindowLatticeUp.mk q s r d w m h c p n)
      rw [stationaryWindowLatticeDecode_encode_bhist q,
        stationaryWindowLatticeDecode_encode_bhist s,
        stationaryWindowLatticeDecode_encode_bhist r,
        stationaryWindowLatticeDecode_encode_bhist d,
        stationaryWindowLatticeDecode_encode_bhist w,
        stationaryWindowLatticeDecode_encode_bhist m,
        stationaryWindowLatticeDecode_encode_bhist h,
        stationaryWindowLatticeDecode_encode_bhist c,
        stationaryWindowLatticeDecode_encode_bhist p,
        stationaryWindowLatticeDecode_encode_bhist n]

private theorem stationaryWindowLatticeToEventFlow_injective
    {x y : StationaryWindowLatticeUp} :
    stationaryWindowLatticeToEventFlow x =
      stationaryWindowLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stationaryWindowLatticeFromEventFlow (stationaryWindowLatticeToEventFlow x) =
        stationaryWindowLatticeFromEventFlow (stationaryWindowLatticeToEventFlow y) :=
    congrArg stationaryWindowLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stationaryWindowLattice_round_trip x).symm
      (Eq.trans hread (stationaryWindowLattice_round_trip y)))

instance stationaryWindowLatticeBHistCarrier :
    BHistCarrier StationaryWindowLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryWindowLatticeToEventFlow
  fromEventFlow := stationaryWindowLatticeFromEventFlow

instance stationaryWindowLatticeChapterTasteGate :
    ChapterTasteGate StationaryWindowLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stationaryWindowLatticeFromEventFlow
        (stationaryWindowLatticeToEventFlow x) = some x
    exact stationaryWindowLattice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stationaryWindowLatticeToEventFlow_injective heq)

theorem StationaryWindowLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist, stationaryWindowLatticeDecodeBHist
      (stationaryWindowLatticeEncodeBHist h) = h) ∧
      (∀ x : StationaryWindowLatticeUp,
        stationaryWindowLatticeFromEventFlow
          (stationaryWindowLatticeToEventFlow x) = some x) ∧
        (∀ x y : StationaryWindowLatticeUp,
          stationaryWindowLatticeToEventFlow x =
            stationaryWindowLatticeToEventFlow y → x = y) ∧
          stationaryWindowLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact stationaryWindowLatticeDecode_encode_bhist
  · constructor
    · exact stationaryWindowLattice_round_trip
    · constructor
      · intro x y heq
        exact stationaryWindowLatticeToEventFlow_injective heq
      · rfl

end BEDC.Derived.StationaryWindowLatticeUp
