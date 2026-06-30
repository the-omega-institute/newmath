import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLimitStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLimitStabilityUp : Type where
  | mk (L0 L1 W R D E0 E1 H C P N : BHist) : RealLimitStabilityUp
  deriving DecidableEq

def realLimitStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLimitStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLimitStabilityEncodeBHist h

def realLimitStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLimitStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLimitStabilityDecodeBHist tail)

private theorem realLimitStability_decode_encode_bhist :
    ∀ h : BHist, realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLimitStabilityFields : RealLimitStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLimitStabilityUp.mk L0 L1 W R D E0 E1 H C P N =>
      [L0, L1, W, R, D, E0, E1, H, C, P, N]

def realLimitStabilityToEventFlow : RealLimitStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realLimitStabilityFields x).map realLimitStabilityEncodeBHist

def realLimitStabilitySplitEventFlow :
    EventFlow →
      Option
        (RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent × RawEvent ×
          RawEvent × RawEvent × RawEvent × RawEvent)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | l0 :: r0 =>
    match r0 with
    | [] => none
    | l1 :: r1 =>
      match r1 with
      | [] => none
      | w :: r2 =>
        match r2 with
        | [] => none
        | r :: r3 =>
          match r3 with
          | [] => none
          | d :: r4 =>
            match r4 with
            | [] => none
            | e0 :: r5 =>
              match r5 with
              | [] => none
              | e1 :: r6 =>
                match r6 with
                | [] => none
                | h :: r7 =>
                  match r7 with
                  | [] => none
                  | c :: r8 =>
                    match r8 with
                    | [] => none
                    | p :: r9 =>
                      match r9 with
                      | [] => none
                      | n :: r10 =>
                        match r10 with
                        | [] =>
                            some (l0, l1, w, r, d, e0, e1, h, c, p, n)
                        | _ :: _ => none

def realLimitStabilityFromEventFlow (ef : EventFlow) : Option RealLimitStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match realLimitStabilitySplitEventFlow ef with
  | some (l0, l1, w, r, d, e0, e1, h, c, p, n) =>
      some
        (RealLimitStabilityUp.mk
          (realLimitStabilityDecodeBHist l0)
          (realLimitStabilityDecodeBHist l1)
          (realLimitStabilityDecodeBHist w)
          (realLimitStabilityDecodeBHist r)
          (realLimitStabilityDecodeBHist d)
          (realLimitStabilityDecodeBHist e0)
          (realLimitStabilityDecodeBHist e1)
          (realLimitStabilityDecodeBHist h)
          (realLimitStabilityDecodeBHist c)
          (realLimitStabilityDecodeBHist p)
          (realLimitStabilityDecodeBHist n))
  | none => none

private theorem realLimitStability_round_trip :
    ∀ x : RealLimitStabilityUp,
      realLimitStabilityFromEventFlow (realLimitStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 W R D E0 E1 H C P N =>
      change
        some
          (RealLimitStabilityUp.mk
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist L0))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist L1))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist W))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist R))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist D))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist E0))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist E1))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist H))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist C))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist P))
            (realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist N))) =
          some (RealLimitStabilityUp.mk L0 L1 W R D E0 E1 H C P N)
      rw [realLimitStability_decode_encode_bhist L0,
        realLimitStability_decode_encode_bhist L1, realLimitStability_decode_encode_bhist W,
        realLimitStability_decode_encode_bhist R, realLimitStability_decode_encode_bhist D,
        realLimitStability_decode_encode_bhist E0, realLimitStability_decode_encode_bhist E1,
        realLimitStability_decode_encode_bhist H, realLimitStability_decode_encode_bhist C,
        realLimitStability_decode_encode_bhist P, realLimitStability_decode_encode_bhist N]

private theorem realLimitStabilityToEventFlow_injective {x y : RealLimitStabilityUp} :
    realLimitStabilityToEventFlow x = realLimitStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLimitStabilityFromEventFlow (realLimitStabilityToEventFlow x) =
        realLimitStabilityFromEventFlow (realLimitStabilityToEventFlow y) :=
    congrArg realLimitStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLimitStability_round_trip x).symm
      (Eq.trans hread (realLimitStability_round_trip y)))

private theorem realLimitStability_fields_faithful :
    ∀ x y : RealLimitStabilityUp,
      realLimitStabilityFields x = realLimitStabilityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L01 L11 W1 R1 D1 E01 E11 H1 C1 P1 N1 =>
      cases y with
      | mk L02 L12 W2 R2 D2 E02 E12 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realLimitStabilityBHistCarrier : BHistCarrier RealLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLimitStabilityToEventFlow
  fromEventFlow := realLimitStabilityFromEventFlow

instance realLimitStabilityChapterTasteGate : ChapterTasteGate RealLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLimitStabilityFromEventFlow (realLimitStabilityToEventFlow x) = some x
    exact realLimitStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLimitStabilityToEventFlow_injective heq)

instance realLimitStabilityFieldFaithful : FieldFaithful RealLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realLimitStabilityFields
  field_faithful := realLimitStability_fields_faithful

instance realLimitStabilityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealLimitStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealLimitStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealLimitStabilityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealLimitStabilityUp) ∧
      Nonempty (FieldFaithful RealLimitStabilityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealLimitStabilityUp) ∧
          (∀ h : BHist,
            realLimitStabilityDecodeBHist (realLimitStabilityEncodeBHist h) = h) ∧
            (∀ x : RealLimitStabilityUp,
              realLimitStabilityFromEventFlow (realLimitStabilityToEventFlow x) = some x) ∧
              (∀ x y : RealLimitStabilityUp,
                realLimitStabilityToEventFlow x = realLimitStabilityToEventFlow y → x = y) ∧
                realLimitStabilityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨realLimitStabilityChapterTasteGate⟩
  · constructor
    · exact ⟨realLimitStabilityFieldFaithful⟩
    · constructor
      · exact ⟨realLimitStabilityNontrivial⟩
      · constructor
        · exact realLimitStability_decode_encode_bhist
        · constructor
          · exact realLimitStability_round_trip
          · constructor
            · intro x y heq
              exact realLimitStabilityToEventFlow_injective heq
            · rfl

end BEDC.Derived.RealLimitStabilityUp
