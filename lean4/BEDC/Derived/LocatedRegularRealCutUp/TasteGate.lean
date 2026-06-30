import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRegularRealCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRegularRealCutUp : Type where
  | mk (L U M D R A H C P N : BHist) : LocatedRegularRealCutUp

def locatedRegularRealCutFields : LocatedRegularRealCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRegularRealCutUp.mk L U M D R A H C P N => [L, U, M, D, R, A, H, C, P, N]

def locatedRegularRealCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRegularRealCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRegularRealCutEncodeBHist h

def locatedRegularRealCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRegularRealCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRegularRealCutDecodeBHist tail)

private theorem locatedRegularRealCutDecode_encode_bhist :
    ∀ h : BHist, locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedRegularRealCutToEventFlow : LocatedRegularRealCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRegularRealCutUp.mk L U M D R A H C P N =>
      [[BMark.b0],
        locatedRegularRealCutEncodeBHist L,
        [BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedRegularRealCutEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedRegularRealCutEncodeBHist N]

private def locatedRegularRealCutEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRegularRealCutEventAtDefault index rest

def locatedRegularRealCutFromEventFlow (ef : EventFlow) : Option LocatedRegularRealCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRegularRealCutUp.mk
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 1 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 3 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 5 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 7 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 9 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 11 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 13 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 15 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 17 ef))
      (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEventAtDefault 19 ef)))

private theorem locatedRegularRealCut_round_trip :
    ∀ x : LocatedRegularRealCutUp,
      locatedRegularRealCutFromEventFlow (locatedRegularRealCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U M D R A H C P N =>
      change
        some
          (LocatedRegularRealCutUp.mk
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist L))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist U))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist M))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist D))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist R))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist A))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist H))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist C))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist P))
            (locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist N))) =
          some (LocatedRegularRealCutUp.mk L U M D R A H C P N)
      rw [locatedRegularRealCutDecode_encode_bhist L,
        locatedRegularRealCutDecode_encode_bhist U,
        locatedRegularRealCutDecode_encode_bhist M,
        locatedRegularRealCutDecode_encode_bhist D,
        locatedRegularRealCutDecode_encode_bhist R,
        locatedRegularRealCutDecode_encode_bhist A,
        locatedRegularRealCutDecode_encode_bhist H,
        locatedRegularRealCutDecode_encode_bhist C,
        locatedRegularRealCutDecode_encode_bhist P,
        locatedRegularRealCutDecode_encode_bhist N]

private theorem locatedRegularRealCutToEventFlow_injective {x y : LocatedRegularRealCutUp} :
    locatedRegularRealCutToEventFlow x = locatedRegularRealCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRegularRealCutFromEventFlow (locatedRegularRealCutToEventFlow x) =
        locatedRegularRealCutFromEventFlow (locatedRegularRealCutToEventFlow y) :=
    congrArg locatedRegularRealCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRegularRealCut_round_trip x).symm
      (Eq.trans hread (locatedRegularRealCut_round_trip y)))

instance locatedRegularRealCutBHistCarrier : BHistCarrier LocatedRegularRealCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRegularRealCutToEventFlow
  fromEventFlow := locatedRegularRealCutFromEventFlow

instance locatedRegularRealCutChapterTasteGate : ChapterTasteGate LocatedRegularRealCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRegularRealCutFromEventFlow (locatedRegularRealCutToEventFlow x) = some x
    exact locatedRegularRealCut_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRegularRealCutToEventFlow_injective heq)

theorem LocatedRegularRealCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRegularRealCutDecodeBHist (locatedRegularRealCutEncodeBHist h) = h) ∧
      (∀ x : LocatedRegularRealCutUp,
        locatedRegularRealCutFromEventFlow (locatedRegularRealCutToEventFlow x) = some x) ∧
        (∀ x y : LocatedRegularRealCutUp,
          locatedRegularRealCutToEventFlow x = locatedRegularRealCutToEventFlow y → x = y) ∧
          (∀ L U M D R A H C P N : BHist,
            locatedRegularRealCutFields (LocatedRegularRealCutUp.mk L U M D R A H C P N) =
              [L, U, M, D, R, A, H, C, P, N]) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedRegularRealCutDecode_encode_bhist
  · constructor
    · exact locatedRegularRealCut_round_trip
    · constructor
      · intro x y heq
        exact locatedRegularRealCutToEventFlow_injective heq
      · intro L U M D R A H C P N
        rfl

end BEDC.Derived.LocatedRegularRealCutUp
