import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMetricUp : Type where
  | mk (s d a z u t r h c p n : BHist) : DyadicMetricUp
  deriving DecidableEq

def dyadicMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMetricEncodeBHist h

def dyadicMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMetricDecodeBHist tail)

private theorem DyadicMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicMetricDecodeBHist (dyadicMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicMetricFields : DyadicMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMetricUp.mk s d a z u t r h c p n => [s, d, a, z, u, t, r, h, c, p, n]

def dyadicMetricToEventFlow : DyadicMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicMetricFields x).map dyadicMetricEncodeBHist

private def dyadicMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicMetricEventAtDefault index rest

def dyadicMetricFromEventFlow (ef : EventFlow) : Option DyadicMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicMetricUp.mk
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 0 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 1 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 2 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 3 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 4 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 5 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 6 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 7 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 8 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 9 ef))
      (dyadicMetricDecodeBHist (dyadicMetricEventAtDefault 10 ef)))

private theorem DyadicMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicMetricUp,
      dyadicMetricFromEventFlow (dyadicMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk s d a z u t r h c p n =>
      change
        some
          (DyadicMetricUp.mk
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist s))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist d))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist a))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist z))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist u))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist t))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist r))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist h))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist c))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist p))
            (dyadicMetricDecodeBHist (dyadicMetricEncodeBHist n))) =
          some (DyadicMetricUp.mk s d a z u t r h c p n)
      rw [DyadicMetricTasteGate_single_carrier_alignment_decode s,
        DyadicMetricTasteGate_single_carrier_alignment_decode d,
        DyadicMetricTasteGate_single_carrier_alignment_decode a,
        DyadicMetricTasteGate_single_carrier_alignment_decode z,
        DyadicMetricTasteGate_single_carrier_alignment_decode u,
        DyadicMetricTasteGate_single_carrier_alignment_decode t,
        DyadicMetricTasteGate_single_carrier_alignment_decode r,
        DyadicMetricTasteGate_single_carrier_alignment_decode h,
        DyadicMetricTasteGate_single_carrier_alignment_decode c,
        DyadicMetricTasteGate_single_carrier_alignment_decode p,
        DyadicMetricTasteGate_single_carrier_alignment_decode n]

private theorem DyadicMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicMetricUp} :
    dyadicMetricToEventFlow x = dyadicMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMetricFromEventFlow (dyadicMetricToEventFlow x) =
        dyadicMetricFromEventFlow (dyadicMetricToEventFlow y) :=
    congrArg dyadicMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicMetricUp, dyadicMetricFields x = dyadicMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk s1 d1 a1 z1 u1 t1 r1 h1 c1 p1 n1 =>
      cases y with
      | mk s2 d2 a2 z2 u2 t2 r2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance dyadicMetricBHistCarrier : BHistCarrier DyadicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMetricToEventFlow
  fromEventFlow := dyadicMetricFromEventFlow

instance dyadicMetricChapterTasteGate : ChapterTasteGate DyadicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicMetricFromEventFlow (dyadicMetricToEventFlow x) = some x
    exact DyadicMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicMetricFieldFaithful : FieldFaithful DyadicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicMetricFields
  field_faithful := DyadicMetricTasteGate_single_carrier_alignment_fields

instance dyadicMetricNontrivial : Nontrivial DyadicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicMetricChapterTasteGate

theorem DyadicMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicMetricDecodeBHist (dyadicMetricEncodeBHist h) = h) ∧
      (∀ x : DyadicMetricUp, dyadicMetricFromEventFlow (dyadicMetricToEventFlow x) = some x) ∧
        (∀ x y : DyadicMetricUp, dyadicMetricToEventFlow x = dyadicMetricToEventFlow y → x = y) ∧
          dyadicMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DyadicMetricTasteGate_single_carrier_alignment_decode,
      DyadicMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DyadicMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicMetricUp
