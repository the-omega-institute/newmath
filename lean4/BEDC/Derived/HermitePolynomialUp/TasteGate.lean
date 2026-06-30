import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HermitePolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HermitePolynomialUp : Type where
  | mk (d H0 H1 R O W Q E T C P N : BHist) : HermitePolynomialUp
  deriving DecidableEq

def hermitePolynomialEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hermitePolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hermitePolynomialEncodeBHist h

def hermitePolynomialDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hermitePolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hermitePolynomialDecodeBHist tail)

private theorem HermitePolynomialTasteGate_single_carrier_alignment_decode :
    forall h : BHist, hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hermitePolynomialFields : HermitePolynomialUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HermitePolynomialUp.mk d H0 H1 R O W Q E T C P N =>
      [d, H0, H1, R, O, W, Q, E, T, C, P, N]

def hermitePolynomialToEventFlow : HermitePolynomialUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hermitePolynomialFields x).map hermitePolynomialEncodeBHist

private def hermitePolynomialEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hermitePolynomialEventAtDefault index rest

def hermitePolynomialFromEventFlow (ef : EventFlow) : Option HermitePolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HermitePolynomialUp.mk
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 0 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 1 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 2 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 3 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 4 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 5 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 6 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 7 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 8 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 9 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 10 ef))
      (hermitePolynomialDecodeBHist (hermitePolynomialEventAtDefault 11 ef)))

private theorem HermitePolynomialTasteGate_single_carrier_alignment_round_trip :
    forall x : HermitePolynomialUp,
      hermitePolynomialFromEventFlow (hermitePolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk d H0 H1 R O W Q E T C P N =>
      change
        some
          (HermitePolynomialUp.mk
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist d))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist H0))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist H1))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist R))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist O))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist W))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist Q))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist E))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist T))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist C))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist P))
            (hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist N))) =
          some (HermitePolynomialUp.mk d H0 H1 R O W Q E T C P N)
      rw [HermitePolynomialTasteGate_single_carrier_alignment_decode d,
        HermitePolynomialTasteGate_single_carrier_alignment_decode H0,
        HermitePolynomialTasteGate_single_carrier_alignment_decode H1,
        HermitePolynomialTasteGate_single_carrier_alignment_decode R,
        HermitePolynomialTasteGate_single_carrier_alignment_decode O,
        HermitePolynomialTasteGate_single_carrier_alignment_decode W,
        HermitePolynomialTasteGate_single_carrier_alignment_decode Q,
        HermitePolynomialTasteGate_single_carrier_alignment_decode E,
        HermitePolynomialTasteGate_single_carrier_alignment_decode T,
        HermitePolynomialTasteGate_single_carrier_alignment_decode C,
        HermitePolynomialTasteGate_single_carrier_alignment_decode P,
        HermitePolynomialTasteGate_single_carrier_alignment_decode N]

private theorem HermitePolynomialTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HermitePolynomialUp} :
    hermitePolynomialToEventFlow x = hermitePolynomialToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hermitePolynomialFromEventFlow (hermitePolynomialToEventFlow x) =
        hermitePolynomialFromEventFlow (hermitePolynomialToEventFlow y) :=
    congrArg hermitePolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HermitePolynomialTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HermitePolynomialTasteGate_single_carrier_alignment_round_trip y)))

private theorem HermitePolynomialTasteGate_single_carrier_alignment_fields :
    forall x y : HermitePolynomialUp, hermitePolynomialFields x = hermitePolynomialFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk d1 H01 H11 R1 O1 W1 Q1 E1 T1 C1 P1 N1 =>
      cases y with
      | mk d2 H02 H12 R2 O2 W2 Q2 E2 T2 C2 P2 N2 =>
          cases h
          rfl

instance hermitePolynomialBHistCarrier : BHistCarrier HermitePolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hermitePolynomialToEventFlow
  fromEventFlow := hermitePolynomialFromEventFlow

instance hermitePolynomialChapterTasteGate : ChapterTasteGate HermitePolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hermitePolynomialFromEventFlow (hermitePolynomialToEventFlow x) = some x
    exact HermitePolynomialTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HermitePolynomialTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hermitePolynomialFieldFaithful : FieldFaithful HermitePolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hermitePolynomialFields
  field_faithful := HermitePolynomialTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate HermitePolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hermitePolynomialChapterTasteGate

theorem HermitePolynomialTasteGate_single_carrier_alignment :
    (forall h : BHist, hermitePolynomialDecodeBHist (hermitePolynomialEncodeBHist h) = h) ∧
      (forall x : HermitePolynomialUp,
        hermitePolynomialFromEventFlow (hermitePolynomialToEventFlow x) = some x) ∧
      (forall x y : HermitePolynomialUp,
        hermitePolynomialToEventFlow x = hermitePolynomialToEventFlow y -> x = y) ∧
      (forall x y : HermitePolynomialUp,
        hermitePolynomialFields x = hermitePolynomialFields y -> x = y) ∧
      hermitePolynomialEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨HermitePolynomialTasteGate_single_carrier_alignment_decode,
      HermitePolynomialTasteGate_single_carrier_alignment_round_trip,
      fun _ _ h => HermitePolynomialTasteGate_single_carrier_alignment_toEventFlow_injective h,
      HermitePolynomialTasteGate_single_carrier_alignment_fields,
      rfl⟩

end BEDC.Derived.HermitePolynomialUp
