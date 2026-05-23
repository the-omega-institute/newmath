import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HilbertCubeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HilbertCubeUp : Type where
  | mk (I W S R E M K T Q N : BHist) : HilbertCubeUp
  deriving DecidableEq

def hilbertCubeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hilbertCubeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hilbertCubeEncodeBHist h

def hilbertCubeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hilbertCubeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hilbertCubeDecodeBHist tail)

private theorem HilbertCubeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hilbertCubeDecodeBHist (hilbertCubeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hilbertCubeFields : HilbertCubeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HilbertCubeUp.mk I W S R E M K T Q N => [I, W, S, R, E, M, K, T, Q, N]

def hilbertCubeToEventFlow : HilbertCubeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hilbertCubeFields x).map hilbertCubeEncodeBHist

private def hilbertCubeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hilbertCubeEventAtDefault index rest

def hilbertCubeFromEventFlow (ef : EventFlow) : Option HilbertCubeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HilbertCubeUp.mk
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 0 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 1 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 2 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 3 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 4 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 5 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 6 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 7 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 8 ef))
      (hilbertCubeDecodeBHist (hilbertCubeEventAtDefault 9 ef)))

private theorem HilbertCubeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HilbertCubeUp,
      hilbertCubeFromEventFlow (hilbertCubeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I W S R E M K T Q N =>
      change
        some
          (HilbertCubeUp.mk
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist I))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist W))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist S))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist R))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist E))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist M))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist K))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist T))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist Q))
            (hilbertCubeDecodeBHist (hilbertCubeEncodeBHist N))) =
          some (HilbertCubeUp.mk I W S R E M K T Q N)
      rw [HilbertCubeTasteGate_single_carrier_alignment_decode I,
        HilbertCubeTasteGate_single_carrier_alignment_decode W,
        HilbertCubeTasteGate_single_carrier_alignment_decode S,
        HilbertCubeTasteGate_single_carrier_alignment_decode R,
        HilbertCubeTasteGate_single_carrier_alignment_decode E,
        HilbertCubeTasteGate_single_carrier_alignment_decode M,
        HilbertCubeTasteGate_single_carrier_alignment_decode K,
        HilbertCubeTasteGate_single_carrier_alignment_decode T,
        HilbertCubeTasteGate_single_carrier_alignment_decode Q,
        HilbertCubeTasteGate_single_carrier_alignment_decode N]

private theorem HilbertCubeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HilbertCubeUp} :
    hilbertCubeToEventFlow x = hilbertCubeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hilbertCubeFromEventFlow (hilbertCubeToEventFlow x) =
        hilbertCubeFromEventFlow (hilbertCubeToEventFlow y) :=
    congrArg hilbertCubeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HilbertCubeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HilbertCubeTasteGate_single_carrier_alignment_round_trip y)))

instance hilbertCubeBHistCarrier : BHistCarrier HilbertCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hilbertCubeToEventFlow
  fromEventFlow := hilbertCubeFromEventFlow

instance hilbertCubeChapterTasteGate : ChapterTasteGate HilbertCubeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hilbertCubeFromEventFlow (hilbertCubeToEventFlow x) = some x
    exact HilbertCubeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HilbertCubeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HilbertCubeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hilbertCubeChapterTasteGate

theorem HilbertCubeTasteGate_single_carrier_alignment :
    (∀ h : BHist, hilbertCubeDecodeBHist (hilbertCubeEncodeBHist h) = h) ∧
      (∀ x : HilbertCubeUp,
        hilbertCubeFromEventFlow (hilbertCubeToEventFlow x) = some x) ∧
        (∀ x y : HilbertCubeUp,
          hilbertCubeToEventFlow x = hilbertCubeToEventFlow y → x = y) ∧
          hilbertCubeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HilbertCubeTasteGate_single_carrier_alignment_decode,
      HilbertCubeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HilbertCubeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HilbertCubeUp
