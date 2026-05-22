import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyUniformityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyUniformityUp : Type where
  | mk (R W D E H C P N : BHist) : RegularCauchyUniformityUp
  deriving DecidableEq

def regularCauchyUniformityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyUniformityEncodeBHist h

def regularCauchyUniformityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyUniformityDecodeBHist tail)

private theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyUniformityFields : RegularCauchyUniformityUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyUniformityUp.mk regular window tolerance entourage transport replay provenance
      localName =>
      [regular, window, tolerance, entourage, transport, replay, provenance, localName]

def regularCauchyUniformityToEventFlow : RegularCauchyUniformityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyUniformityUp.mk regular window tolerance entourage transport replay provenance
      localName =>
      [regularCauchyUniformityEncodeBHist regular, regularCauchyUniformityEncodeBHist window,
        regularCauchyUniformityEncodeBHist tolerance,
        regularCauchyUniformityEncodeBHist entourage,
        regularCauchyUniformityEncodeBHist transport, regularCauchyUniformityEncodeBHist replay,
        regularCauchyUniformityEncodeBHist provenance,
        regularCauchyUniformityEncodeBHist localName]

private def regularCauchyUniformityEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyUniformityEventAt index rest

def regularCauchyUniformityFromEventFlow : EventFlow → Option RegularCauchyUniformityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyUniformityUp.mk
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 0 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 1 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 2 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 3 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 4 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 5 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 6 ef))
        (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEventAt 7 ef)))

private theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyUniformityUp,
      regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk regular window tolerance entourage transport replay provenance localName =>
      change
        some
            (RegularCauchyUniformityUp.mk
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist regular))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist window))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist tolerance))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist entourage))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist transport))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist replay))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist provenance))
              (regularCauchyUniformityDecodeBHist
                (regularCauchyUniformityEncodeBHist localName))) =
          some
            (RegularCauchyUniformityUp.mk regular window tolerance entourage transport replay
              provenance localName)
      rw [RegularCauchyUniformityTasteGate_single_carrier_alignment_decode regular,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode window,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode tolerance,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode entourage,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode transport,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode replay,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode provenance,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode localName]

private theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyUniformityUp} :
    regularCauchyUniformityToEventFlow x = regularCauchyUniformityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) :=
        (RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip x).symm
      _ = regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow y) :=
        congrArg regularCauchyUniformityFromEventFlow hxy
      _ = some y := RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hsome

private theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyUniformityUp,
      regularCauchyUniformityFields x = regularCauchyUniformityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 E2 H2 C2 P2 N2 =>
          injection hfields with hR tail0
          injection tail0 with hW tail1
          injection tail1 with hD tail2
          injection tail2 with hE tail3
          injection tail3 with hH tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hR
          subst hW
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyUniformityBHistCarrier : BHistCarrier RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyUniformityToEventFlow
  fromEventFlow := regularCauchyUniformityFromEventFlow

instance regularCauchyUniformityChapterTasteGate : ChapterTasteGate RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x
    exact RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyUniformityFieldFaithful : FieldFaithful RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyUniformityFields
  field_faithful := RegularCauchyUniformityTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyUniformityNontrivial : Nontrivial RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyUniformityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyUniformityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyUniformityUp,
        regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyUniformityUp,
        regularCauchyUniformityToEventFlow x = regularCauchyUniformityToEventFlow y → x = y) ∧
      regularCauchyUniformityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyUniformityTasteGate_single_carrier_alignment_decode,
      RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip,
      fun _ _ hxy => RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.RegularCauchyUniformityUp
