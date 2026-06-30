import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteOpenCoverNerveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteOpenCoverNerveUp : Type where
  | mk (K O I J B H C P M : BHist) : FiniteOpenCoverNerveUp
  deriving DecidableEq

def finiteOpenCoverNerveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOpenCoverNerveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOpenCoverNerveEncodeBHist h

def finiteOpenCoverNerveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOpenCoverNerveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOpenCoverNerveDecodeBHist tail)

private theorem finiteOpenCoverNerve_decode_encode_bhist :
    ∀ h : BHist,
      finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteOpenCoverNerveFields : FiniteOpenCoverNerveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOpenCoverNerveUp.mk K O I J B H C P M => [K, O, I, J, B, H, C, P, M]

def finiteOpenCoverNerveToEventFlow : FiniteOpenCoverNerveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteOpenCoverNerveFields x).map finiteOpenCoverNerveEncodeBHist

private def finiteOpenCoverNerveEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteOpenCoverNerveEventAt index rest

def finiteOpenCoverNerveFromEventFlow (ef : EventFlow) :
    Option FiniteOpenCoverNerveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteOpenCoverNerveUp.mk
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 0 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 1 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 2 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 3 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 4 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 5 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 6 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 7 ef))
      (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEventAt 8 ef)))

private theorem finiteOpenCoverNerve_round_trip (x : FiniteOpenCoverNerveUp) :
    finiteOpenCoverNerveFromEventFlow
        (finiteOpenCoverNerveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K O I J B H C P M =>
      change
        some
          (FiniteOpenCoverNerveUp.mk
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist K))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist O))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist I))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist J))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist B))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist H))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist C))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist P))
            (finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist M))) =
          some (FiniteOpenCoverNerveUp.mk K O I J B H C P M)
      rw [finiteOpenCoverNerve_decode_encode_bhist K,
        finiteOpenCoverNerve_decode_encode_bhist O,
        finiteOpenCoverNerve_decode_encode_bhist I,
        finiteOpenCoverNerve_decode_encode_bhist J,
        finiteOpenCoverNerve_decode_encode_bhist B,
        finiteOpenCoverNerve_decode_encode_bhist H,
        finiteOpenCoverNerve_decode_encode_bhist C,
        finiteOpenCoverNerve_decode_encode_bhist P,
        finiteOpenCoverNerve_decode_encode_bhist M]

private theorem finiteOpenCoverNerveToEventFlow_injective
    {x y : FiniteOpenCoverNerveUp} :
    finiteOpenCoverNerveToEventFlow x =
      finiteOpenCoverNerveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOpenCoverNerveFromEventFlow (finiteOpenCoverNerveToEventFlow x) =
        finiteOpenCoverNerveFromEventFlow (finiteOpenCoverNerveToEventFlow y) :=
    congrArg finiteOpenCoverNerveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteOpenCoverNerve_round_trip x).symm
      (Eq.trans hread (finiteOpenCoverNerve_round_trip y)))

instance finiteOpenCoverNerveBHistCarrier :
    BHistCarrier FiniteOpenCoverNerveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOpenCoverNerveToEventFlow
  fromEventFlow := finiteOpenCoverNerveFromEventFlow

instance finiteOpenCoverNerveChapterTasteGate :
    ChapterTasteGate FiniteOpenCoverNerveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteOpenCoverNerveFromEventFlow
          (finiteOpenCoverNerveToEventFlow x) =
        some x
    exact finiteOpenCoverNerve_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteOpenCoverNerveToEventFlow_injective heq)

theorem FiniteOpenCoverNerveTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteOpenCoverNerveDecodeBHist (finiteOpenCoverNerveEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteOpenCoverNerveUp) ∧
        Nonempty (ChapterTasteGate FiniteOpenCoverNerveUp) ∧
          finiteOpenCoverNerveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact finiteOpenCoverNerve_decode_encode_bhist
  · constructor
    · exact ⟨finiteOpenCoverNerveBHistCarrier⟩
    · constructor
      · exact ⟨finiteOpenCoverNerveChapterTasteGate⟩
      · rfl

end BEDC.Derived.FiniteOpenCoverNerveUp
