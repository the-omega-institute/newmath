import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardFixedPointModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardFixedPointModulusUp : Type where
  | mk (K I L T R E H C P N : BHist) : PicardFixedPointModulusUp
  deriving DecidableEq

def picardFixedPointModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardFixedPointModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardFixedPointModulusEncodeBHist h

def picardFixedPointModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardFixedPointModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardFixedPointModulusDecodeBHist tail)

private theorem picardFixedPointModulusDecodeEncode :
    ∀ h : BHist,
      picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardFixedPointModulusFields : PicardFixedPointModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardFixedPointModulusUp.mk K I L T R E H C P N => [K, I, L, T, R, E, H, C, P, N]

def picardFixedPointModulusToEventFlow : PicardFixedPointModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (picardFixedPointModulusFields x).map picardFixedPointModulusEncodeBHist

private def picardFixedPointModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => picardFixedPointModulusEventAt index rest

def picardFixedPointModulusFromEventFlow (ef : EventFlow) :
    Option PicardFixedPointModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PicardFixedPointModulusUp.mk
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 0 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 1 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 2 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 3 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 4 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 5 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 6 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 7 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 8 ef))
      (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEventAt 9 ef)))

private theorem picardFixedPointModulusRoundTrip (x : PicardFixedPointModulusUp) :
    picardFixedPointModulusFromEventFlow (picardFixedPointModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K I L T R E H C P N =>
      change
        some
          (PicardFixedPointModulusUp.mk
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist K))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist I))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist L))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist T))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist R))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist E))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist H))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist C))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist P))
            (picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist N))) =
          some (PicardFixedPointModulusUp.mk K I L T R E H C P N)
      rw [picardFixedPointModulusDecodeEncode K,
        picardFixedPointModulusDecodeEncode I,
        picardFixedPointModulusDecodeEncode L,
        picardFixedPointModulusDecodeEncode T,
        picardFixedPointModulusDecodeEncode R,
        picardFixedPointModulusDecodeEncode E,
        picardFixedPointModulusDecodeEncode H,
        picardFixedPointModulusDecodeEncode C,
        picardFixedPointModulusDecodeEncode P,
        picardFixedPointModulusDecodeEncode N]

private theorem picardFixedPointModulusToEventFlow_injective
    {x y : PicardFixedPointModulusUp} :
    picardFixedPointModulusToEventFlow x = picardFixedPointModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardFixedPointModulusFromEventFlow (picardFixedPointModulusToEventFlow x) =
        picardFixedPointModulusFromEventFlow (picardFixedPointModulusToEventFlow y) :=
    congrArg picardFixedPointModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (picardFixedPointModulusRoundTrip x).symm
      (Eq.trans hread (picardFixedPointModulusRoundTrip y)))

instance picardFixedPointModulusBHistCarrier :
    BHistCarrier PicardFixedPointModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardFixedPointModulusToEventFlow
  fromEventFlow := picardFixedPointModulusFromEventFlow

instance picardFixedPointModulusChapterTasteGate :
    ChapterTasteGate PicardFixedPointModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change picardFixedPointModulusFromEventFlow (picardFixedPointModulusToEventFlow x) = some x
    exact picardFixedPointModulusRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (picardFixedPointModulusToEventFlow_injective heq)

theorem PicardFixedPointModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      picardFixedPointModulusDecodeBHist (picardFixedPointModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PicardFixedPointModulusUp) ∧
        Nonempty (ChapterTasteGate PicardFixedPointModulusUp) ∧
          picardFixedPointModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨picardFixedPointModulusDecodeEncode,
      ⟨⟨picardFixedPointModulusBHistCarrier⟩,
        ⟨picardFixedPointModulusChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.PicardFixedPointModulusUp
