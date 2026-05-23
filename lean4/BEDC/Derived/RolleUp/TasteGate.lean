import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RolleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RolleUp : Type where
  | mk (I E F V D W Z H C P N : BHist) : RolleUp
  deriving DecidableEq

def rolleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rolleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rolleEncodeBHist h

def rolleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rolleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rolleDecodeBHist tail)

private theorem rolleDecode_encode_bhist :
    ∀ h : BHist, rolleDecodeBHist (rolleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rolleFields : RolleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RolleUp.mk I E F V D W Z H C P N => [I, E, F, V, D, W, Z, H, C, P, N]

def rolleToEventFlow : RolleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rolleFields x).map rolleEncodeBHist

def rolleFromEventFlow : EventFlow → Option RolleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restE =>
      match restE with
      | [] => none
      | E :: restF =>
          match restF with
          | [] => none
          | F :: restV =>
              match restV with
              | [] => none
              | V :: restD =>
                  match restD with
                  | [] => none
                  | D :: restW =>
                      match restW with
                      | [] => none
                      | W :: restZ =>
                          match restZ with
                          | [] => none
                          | Z :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (RolleUp.mk
                                                      (rolleDecodeBHist I)
                                                      (rolleDecodeBHist E)
                                                      (rolleDecodeBHist F)
                                                      (rolleDecodeBHist V)
                                                      (rolleDecodeBHist D)
                                                      (rolleDecodeBHist W)
                                                      (rolleDecodeBHist Z)
                                                      (rolleDecodeBHist H)
                                                      (rolleDecodeBHist C)
                                                      (rolleDecodeBHist P)
                                                      (rolleDecodeBHist N))
                                              | _ :: _ => none

private theorem rolle_round_trip :
    ∀ x : RolleUp, rolleFromEventFlow (rolleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I E F V D W Z H C P N =>
      change
        some
          (RolleUp.mk
            (rolleDecodeBHist (rolleEncodeBHist I))
            (rolleDecodeBHist (rolleEncodeBHist E))
            (rolleDecodeBHist (rolleEncodeBHist F))
            (rolleDecodeBHist (rolleEncodeBHist V))
            (rolleDecodeBHist (rolleEncodeBHist D))
            (rolleDecodeBHist (rolleEncodeBHist W))
            (rolleDecodeBHist (rolleEncodeBHist Z))
            (rolleDecodeBHist (rolleEncodeBHist H))
            (rolleDecodeBHist (rolleEncodeBHist C))
            (rolleDecodeBHist (rolleEncodeBHist P))
            (rolleDecodeBHist (rolleEncodeBHist N))) =
          some (RolleUp.mk I E F V D W Z H C P N)
      rw [rolleDecode_encode_bhist I, rolleDecode_encode_bhist E,
        rolleDecode_encode_bhist F, rolleDecode_encode_bhist V,
        rolleDecode_encode_bhist D, rolleDecode_encode_bhist W,
        rolleDecode_encode_bhist Z, rolleDecode_encode_bhist H,
        rolleDecode_encode_bhist C, rolleDecode_encode_bhist P,
        rolleDecode_encode_bhist N]

private theorem rolleToEventFlow_injective {x y : RolleUp} :
    rolleToEventFlow x = rolleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rolleFromEventFlow (rolleToEventFlow x) =
        rolleFromEventFlow (rolleToEventFlow y) :=
    congrArg rolleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rolle_round_trip x).symm (Eq.trans hread (rolle_round_trip y)))

private theorem rolle_fields_faithful :
    ∀ x y : RolleUp, rolleFields x = rolleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 E1 F1 V1 D1 W1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 E2 F2 V2 D2 W2 Z2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance rolleBHistCarrier : BHistCarrier RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rolleToEventFlow
  fromEventFlow := rolleFromEventFlow

instance rolleChapterTasteGate : ChapterTasteGate RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rolleFromEventFlow (rolleToEventFlow x) = some x
    exact rolle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rolleToEventFlow_injective heq)

instance rolleFieldFaithful : FieldFaithful RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rolleFields
  field_faithful := rolle_fields_faithful

instance rolleNontrivial : BEDC.Meta.TasteGate.Nontrivial RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RolleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RolleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RolleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rolleChapterTasteGate

namespace TasteGate

theorem RolleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RolleUp) ∧
      Nonempty (FieldFaithful RolleUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RolleUp) ∧
          (∀ h : BHist, rolleDecodeBHist (rolleEncodeBHist h) = h) ∧
            (∀ x : RolleUp, rolleFromEventFlow (rolleToEventFlow x) = some x) ∧
              (∀ x y : RolleUp, rolleToEventFlow x = rolleToEventFlow y → x = y) ∧
                rolleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro rolleChapterTasteGate,
      Nonempty.intro rolleFieldFaithful,
      Nonempty.intro rolleNontrivial,
      rolleDecode_encode_bhist,
      rolle_round_trip,
      (fun _ _ heq => rolleToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.RolleUp
