import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterBaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterBaseUp : Type where
  | mk (I U D M H C P N : BHist) : CauchyFilterBaseUp
  deriving DecidableEq

def cauchyFilterBaseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterBaseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterBaseEncodeBHist h

def cauchyFilterBaseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterBaseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterBaseDecodeBHist tail)

private theorem cauchyFilterBaseDecode_encode_bhist :
    ∀ h : BHist, cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterBaseFields : CauchyFilterBaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterBaseUp.mk I U D M H C P N => [I, U, D, M, H, C, P, N]

def cauchyFilterBaseToEventFlow : CauchyFilterBaseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterBaseFields x).map cauchyFilterBaseEncodeBHist

def cauchyFilterBaseFromEventFlow : EventFlow → Option CauchyFilterBaseUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restU =>
      match restU with
      | [] => none
      | U :: restD =>
          match restD with
          | [] => none
          | D :: restM =>
              match restM with
              | [] => none
              | M :: restH =>
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
                                        (CauchyFilterBaseUp.mk
                                          (cauchyFilterBaseDecodeBHist I)
                                          (cauchyFilterBaseDecodeBHist U)
                                          (cauchyFilterBaseDecodeBHist D)
                                          (cauchyFilterBaseDecodeBHist M)
                                          (cauchyFilterBaseDecodeBHist H)
                                          (cauchyFilterBaseDecodeBHist C)
                                          (cauchyFilterBaseDecodeBHist P)
                                          (cauchyFilterBaseDecodeBHist N))
                                  | _ :: _ => none

private theorem cauchyFilterBase_round_trip :
    ∀ x : CauchyFilterBaseUp,
      cauchyFilterBaseFromEventFlow (cauchyFilterBaseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I U D M H C P N =>
      change
        some
          (CauchyFilterBaseUp.mk
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist I))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist U))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist D))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist M))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist H))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist C))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist P))
            (cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist N))) =
          some (CauchyFilterBaseUp.mk I U D M H C P N)
      rw [cauchyFilterBaseDecode_encode_bhist I, cauchyFilterBaseDecode_encode_bhist U,
        cauchyFilterBaseDecode_encode_bhist D, cauchyFilterBaseDecode_encode_bhist M,
        cauchyFilterBaseDecode_encode_bhist H, cauchyFilterBaseDecode_encode_bhist C,
        cauchyFilterBaseDecode_encode_bhist P, cauchyFilterBaseDecode_encode_bhist N]

private theorem cauchyFilterBaseToEventFlow_injective {x y : CauchyFilterBaseUp} :
    cauchyFilterBaseToEventFlow x = cauchyFilterBaseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterBaseFromEventFlow (cauchyFilterBaseToEventFlow x) =
        cauchyFilterBaseFromEventFlow (cauchyFilterBaseToEventFlow y) :=
    congrArg cauchyFilterBaseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterBase_round_trip x).symm
      (Eq.trans hread (cauchyFilterBase_round_trip y)))

private theorem cauchyFilterBase_fields_faithful :
    ∀ x y : CauchyFilterBaseUp,
      cauchyFilterBaseFields x = cauchyFilterBaseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 U1 D1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 U2 D2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyFilterBaseBHistCarrier : BHistCarrier CauchyFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterBaseToEventFlow
  fromEventFlow := cauchyFilterBaseFromEventFlow

instance cauchyFilterBaseChapterTasteGate : ChapterTasteGate CauchyFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterBaseFromEventFlow (cauchyFilterBaseToEventFlow x) = some x
    exact cauchyFilterBase_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterBaseToEventFlow_injective heq)

instance cauchyFilterBaseFieldFaithful : FieldFaithful CauchyFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterBaseFields
  field_faithful := cauchyFilterBase_fields_faithful

instance cauchyFilterBaseNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyFilterBaseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyFilterBaseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyFilterBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterBaseChapterTasteGate

namespace TasteGate

theorem CauchyFilterBaseTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyFilterBaseUp) ∧
      Nonempty (FieldFaithful CauchyFilterBaseUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyFilterBaseUp) ∧
          (∀ h : BHist, cauchyFilterBaseDecodeBHist (cauchyFilterBaseEncodeBHist h) = h) ∧
            (∀ x : CauchyFilterBaseUp,
              cauchyFilterBaseFromEventFlow (cauchyFilterBaseToEventFlow x) = some x) ∧
              (∀ x y : CauchyFilterBaseUp,
                cauchyFilterBaseToEventFlow x = cauchyFilterBaseToEventFlow y → x = y) ∧
                cauchyFilterBaseEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro cauchyFilterBaseChapterTasteGate,
      Nonempty.intro cauchyFilterBaseFieldFaithful,
      Nonempty.intro cauchyFilterBaseNontrivial,
      cauchyFilterBaseDecode_encode_bhist,
      cauchyFilterBase_round_trip,
      (fun _ _ heq => cauchyFilterBaseToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.CauchyFilterBaseUp
