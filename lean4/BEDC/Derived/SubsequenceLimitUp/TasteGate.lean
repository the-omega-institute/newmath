import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubsequenceLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubsequenceLimitUp : Type where
  | mk (parent selector tolerance realSeal h c p n : BHist) : SubsequenceLimitUp
  deriving DecidableEq

def subsequenceLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subsequenceLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subsequenceLimitEncodeBHist h

def subsequenceLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subsequenceLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subsequenceLimitDecodeBHist tail)

private theorem subsequenceLimitDecode_encode_bhist :
    ∀ h : BHist, subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subsequenceLimitFields : SubsequenceLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubsequenceLimitUp.mk parent selector tolerance realSeal h c p n =>
      [parent, selector, tolerance, realSeal, h, c, p, n]

def subsequenceLimitToEventFlow : SubsequenceLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (subsequenceLimitFields x).map subsequenceLimitEncodeBHist

def subsequenceLimitFromEventFlow : EventFlow → Option SubsequenceLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | parent :: selector :: tolerance :: realSeal :: h :: c :: p :: n :: [] =>
      some
        (SubsequenceLimitUp.mk
          (subsequenceLimitDecodeBHist parent)
          (subsequenceLimitDecodeBHist selector)
          (subsequenceLimitDecodeBHist tolerance)
          (subsequenceLimitDecodeBHist realSeal)
          (subsequenceLimitDecodeBHist h)
          (subsequenceLimitDecodeBHist c)
          (subsequenceLimitDecodeBHist p)
          (subsequenceLimitDecodeBHist n))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _rest => none

private theorem subsequenceLimit_round_trip :
    ∀ x : SubsequenceLimitUp,
      subsequenceLimitFromEventFlow (subsequenceLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parent selector tolerance realSeal h c p n =>
      change
        some
          (SubsequenceLimitUp.mk
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist parent))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist selector))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist tolerance))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist realSeal))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist h))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist c))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist p))
            (subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist n))) =
          some (SubsequenceLimitUp.mk parent selector tolerance realSeal h c p n)
      rw [subsequenceLimitDecode_encode_bhist parent,
        subsequenceLimitDecode_encode_bhist selector,
        subsequenceLimitDecode_encode_bhist tolerance,
        subsequenceLimitDecode_encode_bhist realSeal,
        subsequenceLimitDecode_encode_bhist h,
        subsequenceLimitDecode_encode_bhist c,
        subsequenceLimitDecode_encode_bhist p,
        subsequenceLimitDecode_encode_bhist n]

private theorem subsequenceLimitToEventFlow_injective {x y : SubsequenceLimitUp} :
    subsequenceLimitToEventFlow x = subsequenceLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subsequenceLimitFromEventFlow (subsequenceLimitToEventFlow x) =
        subsequenceLimitFromEventFlow (subsequenceLimitToEventFlow y) :=
    congrArg subsequenceLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subsequenceLimit_round_trip x).symm
      (Eq.trans hread (subsequenceLimit_round_trip y)))

instance subsequenceLimitBHistCarrier : BHistCarrier SubsequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subsequenceLimitToEventFlow
  fromEventFlow := subsequenceLimitFromEventFlow

instance subsequenceLimitChapterTasteGate : ChapterTasteGate SubsequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subsequenceLimitFromEventFlow (subsequenceLimitToEventFlow x) = some x
    exact subsequenceLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subsequenceLimitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SubsequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subsequenceLimitChapterTasteGate

theorem SubsequenceLimitTasteGate_single_carrier_alignment
    (parent selector tolerance realSeal h c p n : BHist) :
    subsequenceLimitDecodeBHist (subsequenceLimitEncodeBHist parent) = parent ∧
      subsequenceLimitEncodeBHist BHist.Empty = ([] : List BMark) ∧
        BHistCarrier.fromEventFlow
            (BHistCarrier.toEventFlow
              (SubsequenceLimitUp.mk parent selector tolerance realSeal h c p n)) =
          some (SubsequenceLimitUp.mk parent selector tolerance realSeal h c p n) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨subsequenceLimitDecode_encode_bhist parent, rfl,
      ChapterTasteGate.round_trip
        (SubsequenceLimitUp.mk parent selector tolerance realSeal h c p n)⟩

end BEDC.Derived.SubsequenceLimitUp
