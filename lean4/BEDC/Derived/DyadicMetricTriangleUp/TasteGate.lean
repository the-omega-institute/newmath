import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMetricTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMetricTriangleUp : Type where
  | mk (x y z dxy dyz dxz a b t h c p n : BHist) : DyadicMetricTriangleUp
  deriving DecidableEq

def dyadicMetricTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMetricTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMetricTriangleEncodeBHist h

def dyadicMetricTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMetricTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMetricTriangleDecodeBHist tail)

private theorem DyadicMetricTriangleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hist
  induction hist with
  | Empty => rfl
  | e0 hist ih => exact congrArg BHist.e0 ih
  | e1 hist ih => exact congrArg BHist.e1 ih

def dyadicMetricTriangleFields : DyadicMetricTriangleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMetricTriangleUp.mk x y z dxy dyz dxz a b t h c p n =>
      [x, y, z, dxy, dyz, dxz, a, b, t, h, c, p, n]

def dyadicMetricTriangleToEventFlow : DyadicMetricTriangleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun token => (dyadicMetricTriangleFields token).map dyadicMetricTriangleEncodeBHist

private def dyadicMetricTriangleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicMetricTriangleEventAtDefault index rest

def dyadicMetricTriangleFromEventFlow (ef : EventFlow) : Option DyadicMetricTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicMetricTriangleUp.mk
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 0 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 1 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 2 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 3 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 4 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 5 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 6 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 7 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 8 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 9 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 10 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 11 ef))
      (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEventAtDefault 12 ef)))

private theorem DyadicMetricTriangleTasteGate_single_carrier_alignment_round_trip :
    ∀ token : DyadicMetricTriangleUp,
      dyadicMetricTriangleFromEventFlow (dyadicMetricTriangleToEventFlow token) =
        some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk x y z dxy dyz dxz a b t h c p n =>
      change
        some
          (DyadicMetricTriangleUp.mk
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist x))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist y))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist z))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist dxy))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist dyz))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist dxz))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist a))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist b))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist t))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist h))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist c))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist p))
            (dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist n))) =
          some (DyadicMetricTriangleUp.mk x y z dxy dyz dxz a b t h c p n)
      rw [DyadicMetricTriangleTasteGate_single_carrier_alignment_decode x,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode y,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode z,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode dxy,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode dyz,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode dxz,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode a,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode b,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode t,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode h,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode c,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode p,
        DyadicMetricTriangleTasteGate_single_carrier_alignment_decode n]

private theorem DyadicMetricTriangleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicMetricTriangleUp} :
    dyadicMetricTriangleToEventFlow x = dyadicMetricTriangleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMetricTriangleFromEventFlow (dyadicMetricTriangleToEventFlow x) =
        dyadicMetricTriangleFromEventFlow (dyadicMetricTriangleToEventFlow y) :=
    congrArg dyadicMetricTriangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicMetricTriangleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicMetricTriangleTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicMetricTriangleBHistCarrier : BHistCarrier DyadicMetricTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMetricTriangleToEventFlow
  fromEventFlow := dyadicMetricTriangleFromEventFlow

instance dyadicMetricTriangleChapterTasteGate :
    ChapterTasteGate DyadicMetricTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro token
    change dyadicMetricTriangleFromEventFlow (dyadicMetricTriangleToEventFlow token) =
      some token
    exact DyadicMetricTriangleTasteGate_single_carrier_alignment_round_trip token
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicMetricTriangleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicMetricTriangleTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicMetricTriangleDecodeBHist (dyadicMetricTriangleEncodeBHist h) = h) ∧
      (∀ x : DyadicMetricTriangleUp,
        dyadicMetricTriangleFromEventFlow (dyadicMetricTriangleToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier DyadicMetricTriangleUp) ∧
          Nonempty (ChapterTasteGate DyadicMetricTriangleUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨DyadicMetricTriangleTasteGate_single_carrier_alignment_decode,
      DyadicMetricTriangleTasteGate_single_carrier_alignment_round_trip,
      ⟨dyadicMetricTriangleBHistCarrier⟩,
      ⟨dyadicMetricTriangleChapterTasteGate⟩⟩

end BEDC.Derived.DyadicMetricTriangleUp
