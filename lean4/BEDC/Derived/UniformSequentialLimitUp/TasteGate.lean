import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformSequentialLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformSequentialLimitUp : Type where
  | mk (S M V R E H C P N : BHist) : UniformSequentialLimitUp
  deriving DecidableEq

def uniformSequentialLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformSequentialLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformSequentialLimitEncodeBHist h

def uniformSequentialLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformSequentialLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformSequentialLimitDecodeBHist tail)

private theorem uniformSequentialLimitDecodeEncode :
    ∀ h : BHist,
      uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformSequentialLimitFields : UniformSequentialLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformSequentialLimitUp.mk S M V R E H C P N => [S, M, V, R, E, H, C, P, N]

def uniformSequentialLimitToEventFlow : UniformSequentialLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformSequentialLimitFields x).map uniformSequentialLimitEncodeBHist

private def uniformSequentialLimitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformSequentialLimitEventAt index rest

def uniformSequentialLimitFromEventFlow
    (flow : EventFlow) : Option UniformSequentialLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformSequentialLimitUp.mk
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 0 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 1 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 2 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 3 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 4 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 5 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 6 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 7 flow))
      (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEventAt 8 flow)))

private theorem uniformSequentialLimitRoundTrip
    (x : UniformSequentialLimitUp) :
    uniformSequentialLimitFromEventFlow (uniformSequentialLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M V R E H C P N =>
      change
        some
          (UniformSequentialLimitUp.mk
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist S))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist M))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist V))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist R))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist E))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist H))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist C))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist P))
            (uniformSequentialLimitDecodeBHist (uniformSequentialLimitEncodeBHist N))) =
          some (UniformSequentialLimitUp.mk S M V R E H C P N)
      rw [uniformSequentialLimitDecodeEncode S, uniformSequentialLimitDecodeEncode M,
        uniformSequentialLimitDecodeEncode V, uniformSequentialLimitDecodeEncode R,
        uniformSequentialLimitDecodeEncode E, uniformSequentialLimitDecodeEncode H,
        uniformSequentialLimitDecodeEncode C, uniformSequentialLimitDecodeEncode P,
        uniformSequentialLimitDecodeEncode N]

private theorem uniformSequentialLimitToEventFlow_injective {x y : UniformSequentialLimitUp} :
    uniformSequentialLimitToEventFlow x = uniformSequentialLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformSequentialLimitFromEventFlow (uniformSequentialLimitToEventFlow x) =
        uniformSequentialLimitFromEventFlow (uniformSequentialLimitToEventFlow y) :=
    congrArg uniformSequentialLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformSequentialLimitRoundTrip x).symm
      (Eq.trans hread (uniformSequentialLimitRoundTrip y)))

instance uniformSequentialLimitBHistCarrier : BHistCarrier UniformSequentialLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformSequentialLimitToEventFlow
  fromEventFlow := uniformSequentialLimitFromEventFlow

instance uniformSequentialLimitChapterTasteGate :
    ChapterTasteGate UniformSequentialLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformSequentialLimitFromEventFlow (uniformSequentialLimitToEventFlow x) = some x
    exact uniformSequentialLimitRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformSequentialLimitToEventFlow_injective heq)

theorem UniformSequentialLimitTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier UniformSequentialLimitUp) ∧
      Nonempty (ChapterTasteGate UniformSequentialLimitUp) ∧
        (∀ x : UniformSequentialLimitUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (∃ x : UniformSequentialLimitUp,
            List.Mem ([BMark.b1] : RawEvent) (BHistCarrier.toEventFlow x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  refine
    ⟨⟨uniformSequentialLimitBHistCarrier⟩, ⟨uniformSequentialLimitChapterTasteGate⟩, ?_,
      ?_⟩
  · intro x
    change uniformSequentialLimitFromEventFlow (uniformSequentialLimitToEventFlow x) = some x
    exact uniformSequentialLimitRoundTrip x
  · exact
      ⟨UniformSequentialLimitUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
          simp only [BHistCarrier.toEventFlow, uniformSequentialLimitToEventFlow,
            uniformSequentialLimitFields]
          exact List.Mem.head _⟩

end BEDC.Derived.UniformSequentialLimitUp
