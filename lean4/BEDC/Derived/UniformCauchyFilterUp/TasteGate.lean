import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyFilterUp : Type where
  | mk (U F C T S R E H K P N : BHist) : UniformCauchyFilterUp
  deriving DecidableEq

def uniformCauchyFilterEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyFilterEncodeBHist h

def uniformCauchyFilterDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyFilterDecodeBHist tail)

private theorem uniformCauchyFilterDecode_encode_bhist :
    forall h : BHist,
      uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformCauchyFilterToEventFlow : UniformCauchyFilterUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyFilterUp.mk U F C T S R E H K P N =>
      [[BMark.b0],
        uniformCauchyFilterEncodeBHist U,
        [BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        uniformCauchyFilterEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyFilterEncodeBHist N]

private def uniformCauchyFilterEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, row :: _ => row
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => uniformCauchyFilterEventAtDefault n rest

def uniformCauchyFilterFromEventFlow (ef : EventFlow) : Option UniformCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchyFilterUp.mk
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 1 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 3 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 5 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 7 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 9 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 11 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 13 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 15 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 17 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 19 ef))
      (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEventAtDefault 21 ef)))

private theorem uniformCauchyFilter_round_trip :
    forall x : UniformCauchyFilterUp,
      uniformCauchyFilterFromEventFlow (uniformCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U F C T S R E H K P N =>
      change
        some
          (UniformCauchyFilterUp.mk
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist U))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist F))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist C))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N))) =
          some (UniformCauchyFilterUp.mk U F C T S R E H K P N)
      exact congrArg some (calc
        UniformCauchyFilterUp.mk
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist U))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist F))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist C))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) =
          UniformCauchyFilterUp.mk U
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist F))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist C))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist F))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist C))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist U)
        _ = UniformCauchyFilterUp.mk U F
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist C))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist C))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist F)
        _ = UniformCauchyFilterUp.mk U F C
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist T))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist C)
        _ = UniformCauchyFilterUp.mk U F C T
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist S))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist T)
        _ = UniformCauchyFilterUp.mk U F C T S
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist R))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist S)
        _ = UniformCauchyFilterUp.mk U F C T S R
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T S z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist E))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist R)
        _ = UniformCauchyFilterUp.mk U F C T S R E
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T S R z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist H))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist E)
        _ = UniformCauchyFilterUp.mk U F C T S R E H
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T S R E z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist K))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist H)
        _ = UniformCauchyFilterUp.mk U F C T S R E H K
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T S R E H z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist P))
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist K)
        _ = UniformCauchyFilterUp.mk U F C T S R E H K P
            (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)) :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T S R E H K z
              (uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist N)))
            (uniformCauchyFilterDecode_encode_bhist P)
        _ = UniformCauchyFilterUp.mk U F C T S R E H K P N :=
          congrArg
            (fun z => UniformCauchyFilterUp.mk U F C T S R E H K P z)
            (uniformCauchyFilterDecode_encode_bhist N))

private theorem uniformCauchyFilterToEventFlow_injective {x y : UniformCauchyFilterUp} :
    uniformCauchyFilterToEventFlow x = uniformCauchyFilterToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyFilterFromEventFlow (uniformCauchyFilterToEventFlow x) =
        uniformCauchyFilterFromEventFlow (uniformCauchyFilterToEventFlow y) :=
    congrArg uniformCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchyFilter_round_trip x).symm
      (Eq.trans hread (uniformCauchyFilter_round_trip y)))

instance uniformCauchyFilterBHistCarrier : BHistCarrier UniformCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyFilterToEventFlow
  fromEventFlow := uniformCauchyFilterFromEventFlow

instance uniformCauchyFilterChapterTasteGate : ChapterTasteGate UniformCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCauchyFilterFromEventFlow (uniformCauchyFilterToEventFlow x) = some x
    exact uniformCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchyFilterToEventFlow_injective heq)

theorem UniformCauchyFilterTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformCauchyFilterDecodeBHist (uniformCauchyFilterEncodeBHist h) = h) /\
      (forall x : UniformCauchyFilterUp,
        uniformCauchyFilterFromEventFlow (uniformCauchyFilterToEventFlow x) = some x) /\
        (forall x y : UniformCauchyFilterUp,
          uniformCauchyFilterToEventFlow x = uniformCauchyFilterToEventFlow y -> x = y) /\
          uniformCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact uniformCauchyFilterDecode_encode_bhist
  · constructor
    · exact uniformCauchyFilter_round_trip
    · constructor
      · intro x y heq
        exact uniformCauchyFilterToEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformCauchyFilterUp
