import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCommonRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCommonRefinementUp : Type where
  | mk (S0 S1 I M0 Q0 M1 Q1 W D R A H C P N : BHist) :
      RegularCauchyCommonRefinementUp
  deriving DecidableEq

def regularCauchyCommonRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCommonRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCommonRefinementEncodeBHist h

def regularCauchyCommonRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCommonRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCommonRefinementDecodeBHist tail)

private theorem RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCommonRefinementFields :
    RegularCauchyCommonRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCommonRefinementUp.mk S0 S1 I M0 Q0 M1 Q1 W D R A H C P N =>
      [S0, S1, I, M0, Q0, M1, Q1, W, D, R, A, H, C, P, N]

def regularCauchyCommonRefinementToEventFlow :
    RegularCauchyCommonRefinementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyCommonRefinementFields x).map
    regularCauchyCommonRefinementEncodeBHist

private def regularCauchyCommonRefinementEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCommonRefinementEventAtDefault index rest

def regularCauchyCommonRefinementFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCommonRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCommonRefinementUp.mk
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 0 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 1 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 2 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 3 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 4 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 5 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 6 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 7 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 8 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 9 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 10 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 11 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 12 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 13 ef))
      (regularCauchyCommonRefinementDecodeBHist
        (regularCauchyCommonRefinementEventAtDefault 14 ef)))

private theorem RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCommonRefinementUp,
      regularCauchyCommonRefinementFromEventFlow
        (regularCauchyCommonRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S0 S1 I M0 Q0 M1 Q1 W D R A H C P N =>
      change
        some
          (RegularCauchyCommonRefinementUp.mk
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist S0))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist S1))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist I))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist M0))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist Q0))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist M1))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist Q1))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist W))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist D))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist R))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist A))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist H))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist C))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist P))
            (regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist N))) =
          some (RegularCauchyCommonRefinementUp.mk S0 S1 I M0 Q0 M1 Q1 W D R A H C P N)
      rw [RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode S0,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode S1,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode I,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode M0,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode Q0,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode M1,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode Q1,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode W,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode D,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode R,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode A,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCommonRefinementUp} :
    regularCauchyCommonRefinementToEventFlow x =
      regularCauchyCommonRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCommonRefinementFromEventFlow
          (regularCauchyCommonRefinementToEventFlow x) =
        regularCauchyCommonRefinementFromEventFlow
          (regularCauchyCommonRefinementToEventFlow y) :=
    congrArg regularCauchyCommonRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyCommonRefinementUp,
      regularCauchyCommonRefinementFields x =
        regularCauchyCommonRefinementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S01 S11 I1 M01 Q01 M11 Q11 W1 D1 R1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk S02 S12 I2 M02 Q02 M12 Q12 W2 D2 R2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyCommonRefinementBHistCarrier :
    BHistCarrier RegularCauchyCommonRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCommonRefinementToEventFlow
  fromEventFlow := regularCauchyCommonRefinementFromEventFlow

instance regularCauchyCommonRefinementChapterTasteGate :
    ChapterTasteGate RegularCauchyCommonRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCommonRefinementFromEventFlow
        (regularCauchyCommonRefinementToEventFlow x) = some x
    exact RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyCommonRefinementFieldFaithful :
    FieldFaithful RegularCauchyCommonRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCommonRefinementFields
  field_faithful := RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_fields

instance regularCauchyCommonRefinementNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyCommonRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCommonRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCommonRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCommonRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCommonRefinementChapterTasteGate

theorem RegularCauchyCommonRefinementTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyCommonRefinementUp) ∧
      Nonempty (FieldFaithful RegularCauchyCommonRefinementUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyCommonRefinementUp) ∧
          (∀ h : BHist,
            regularCauchyCommonRefinementDecodeBHist
              (regularCauchyCommonRefinementEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyCommonRefinementUp,
              regularCauchyCommonRefinementFromEventFlow
                (regularCauchyCommonRefinementToEventFlow x) = some x) ∧
              (∀ x y : RegularCauchyCommonRefinementUp,
                regularCauchyCommonRefinementToEventFlow x =
                  regularCauchyCommonRefinementToEventFlow y → x = y) ∧
                regularCauchyCommonRefinementEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyCommonRefinementChapterTasteGate⟩,
      ⟨regularCauchyCommonRefinementFieldFaithful⟩,
      ⟨regularCauchyCommonRefinementNontrivial⟩,
      RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_decode,
      RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyCommonRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCommonRefinementUp
