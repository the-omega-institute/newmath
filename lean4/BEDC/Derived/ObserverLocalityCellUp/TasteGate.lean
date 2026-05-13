import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# ObserverLocalityCellUp TasteGate carrier.
-/

namespace BEDC.Derived.ObserverLocalityCellUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite two-observer locality-cell packet with the ten displayed BEDC rows. -/
inductive ObserverLocalityCellUp : Type where
  | mk :
      (observerLeft observerRight eventLeft eventRight gapLeft gapRight transport
        continuation provenance nameCert : BHist) →
      ObserverLocalityCellUp
  deriving DecidableEq

def observerLocalityCellEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerLocalityCellEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerLocalityCellEncodeBHist h

def observerLocalityCellDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerLocalityCellDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerLocalityCellDecodeBHist tail)

private theorem observerLocalityCellDecodeEncodeBHist :
    ∀ h : BHist, observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerLocalityCellToEventFlow : ObserverLocalityCellUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverLocalityCellUp.mk observerLeft observerRight eventLeft eventRight gapLeft gapRight
      transport continuation provenance nameCert =>
      [[BMark.b0],
        observerLocalityCellEncodeBHist observerLeft,
        [BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist observerRight,
        [BMark.b1, BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist eventLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist eventRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist gapLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist gapRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerLocalityCellEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observerLocalityCellEncodeBHist nameCert]

def observerLocalityCellFromEventFlow : EventFlow → Option ObserverLocalityCellUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observerRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | eventLeft :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | eventRight :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gapLeft :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | gapRight :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ObserverLocalityCellUp.mk
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            observerLeft)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            observerRight)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            eventLeft)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            eventRight)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            gapLeft)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            gapRight)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            transport)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            continuation)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            provenance)
                                                                                          (observerLocalityCellDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem observerLocalityCellRoundTrip :
    ∀ x : ObserverLocalityCellUp,
      observerLocalityCellFromEventFlow (observerLocalityCellToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert =>
      change
        some
          (ObserverLocalityCellUp.mk
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist observerLeft))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist observerRight))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist eventLeft))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist eventRight))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist gapLeft))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist gapRight))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist transport))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist continuation))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist provenance))
            (observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist nameCert))) =
          some
            (ObserverLocalityCellUp.mk observerLeft observerRight eventLeft eventRight gapLeft
              gapRight transport continuation provenance nameCert)
      rw [observerLocalityCellDecodeEncodeBHist observerLeft,
        observerLocalityCellDecodeEncodeBHist observerRight,
        observerLocalityCellDecodeEncodeBHist eventLeft,
        observerLocalityCellDecodeEncodeBHist eventRight,
        observerLocalityCellDecodeEncodeBHist gapLeft,
        observerLocalityCellDecodeEncodeBHist gapRight,
        observerLocalityCellDecodeEncodeBHist transport,
        observerLocalityCellDecodeEncodeBHist continuation,
        observerLocalityCellDecodeEncodeBHist provenance,
        observerLocalityCellDecodeEncodeBHist nameCert]

private theorem observerLocalityCellToEventFlow_injective {x y : ObserverLocalityCellUp} :
    observerLocalityCellToEventFlow x = observerLocalityCellToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerLocalityCellFromEventFlow (observerLocalityCellToEventFlow x) =
        observerLocalityCellFromEventFlow (observerLocalityCellToEventFlow y) :=
    congrArg observerLocalityCellFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerLocalityCellRoundTrip x).symm
      (Eq.trans hread (observerLocalityCellRoundTrip y)))

instance observerLocalityCellBHistCarrier : BHistCarrier ObserverLocalityCellUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerLocalityCellToEventFlow
  fromEventFlow := observerLocalityCellFromEventFlow

instance observerLocalityCellChapterTasteGate : ChapterTasteGate ObserverLocalityCellUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerLocalityCellFromEventFlow (observerLocalityCellToEventFlow x) = some x
    exact observerLocalityCellRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerLocalityCellToEventFlow_injective heq)

theorem ObserverLocalityCellTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerLocalityCellDecodeBHist (observerLocalityCellEncodeBHist h) = h) ∧
      (∀ x : ObserverLocalityCellUp,
        observerLocalityCellFromEventFlow (observerLocalityCellToEventFlow x) = some x) ∧
        (∀ x y : ObserverLocalityCellUp,
          observerLocalityCellToEventFlow x = observerLocalityCellToEventFlow y → x = y) ∧
          observerLocalityCellEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerLocalityCellDecodeEncodeBHist
  · constructor
    · exact observerLocalityCellRoundTrip
    · constructor
      · intro x y heq
        exact observerLocalityCellToEventFlow_injective heq
      · rfl

def taste_gate : ChapterTasteGate ObserverLocalityCellUp :=
  observerLocalityCellChapterTasteGate

end BEDC.Derived.ObserverLocalityCellUp
