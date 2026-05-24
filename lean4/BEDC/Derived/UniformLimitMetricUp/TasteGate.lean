import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitMetricUp : Type where
  | mk (M F U B R E H C P N : BHist) : UniformLimitMetricUp
  deriving DecidableEq

def uniformLimitMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitMetricEncodeBHist h

def uniformLimitMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitMetricDecodeBHist tail)

private theorem UniformLimitMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLimitMetricFields : UniformLimitMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitMetricUp.mk M F U B R E H C P N => [M, F, U, B, R, E, H, C, P, N]

def uniformLimitMetricToEventFlow : UniformLimitMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLimitMetricFields x).map uniformLimitMetricEncodeBHist

def uniformLimitMetricFromEventFlow : EventFlow → Option UniformLimitMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _M :: [] => none
  | _M :: _F :: [] => none
  | _M :: _F :: _U :: [] => none
  | _M :: _F :: _U :: _B :: [] => none
  | _M :: _F :: _U :: _B :: _R :: [] => none
  | _M :: _F :: _U :: _B :: _R :: _E :: [] => none
  | _M :: _F :: _U :: _B :: _R :: _E :: _H :: [] => none
  | _M :: _F :: _U :: _B :: _R :: _E :: _H :: _C :: [] => none
  | _M :: _F :: _U :: _B :: _R :: _E :: _H :: _C :: _P :: [] => none
  | M :: F :: U :: B :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (UniformLimitMetricUp.mk
          (uniformLimitMetricDecodeBHist M)
          (uniformLimitMetricDecodeBHist F)
          (uniformLimitMetricDecodeBHist U)
          (uniformLimitMetricDecodeBHist B)
          (uniformLimitMetricDecodeBHist R)
          (uniformLimitMetricDecodeBHist E)
          (uniformLimitMetricDecodeBHist H)
          (uniformLimitMetricDecodeBHist C)
          (uniformLimitMetricDecodeBHist P)
          (uniformLimitMetricDecodeBHist N))
  | _M :: _F :: _U :: _B :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem UniformLimitMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformLimitMetricUp,
      uniformLimitMetricFromEventFlow (uniformLimitMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F U B R E H C P N =>
      change
        some
          (UniformLimitMetricUp.mk
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist M))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist F))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist U))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist B))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist R))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist E))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist H))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist C))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist P))
            (uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist N))) =
          some (UniformLimitMetricUp.mk M F U B R E H C P N)
      rw [UniformLimitMetricTasteGate_single_carrier_alignment_decode M,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode F,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode U,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode B,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode R,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode E,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode H,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode C,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode P,
        UniformLimitMetricTasteGate_single_carrier_alignment_decode N]

private theorem UniformLimitMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformLimitMetricUp} :
    uniformLimitMetricToEventFlow x = uniformLimitMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitMetricFromEventFlow (uniformLimitMetricToEventFlow x) =
        uniformLimitMetricFromEventFlow (uniformLimitMetricToEventFlow y) :=
    congrArg uniformLimitMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformLimitMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformLimitMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformLimitMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformLimitMetricUp, uniformLimitMetricFields x = uniformLimitMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 F1 U1 B1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 F2 U2 B2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformLimitMetricBHistCarrier : BHistCarrier UniformLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitMetricToEventFlow
  fromEventFlow := uniformLimitMetricFromEventFlow

instance uniformLimitMetricChapterTasteGate : ChapterTasteGate UniformLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLimitMetricFromEventFlow (uniformLimitMetricToEventFlow x) = some x
    exact UniformLimitMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformLimitMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformLimitMetricFieldFaithful : FieldFaithful UniformLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitMetricFields
  field_faithful := UniformLimitMetricTasteGate_single_carrier_alignment_fields

instance uniformLimitMetricNontrivial : Nontrivial UniformLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitMetricChapterTasteGate

theorem UniformLimitMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformLimitMetricDecodeBHist (uniformLimitMetricEncodeBHist h) = h) ∧
      (∀ x : UniformLimitMetricUp,
        uniformLimitMetricFromEventFlow (uniformLimitMetricToEventFlow x) = some x) ∧
        (∀ x y : UniformLimitMetricUp,
          uniformLimitMetricToEventFlow x = uniformLimitMetricToEventFlow y → x = y) ∧
          uniformLimitMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨UniformLimitMetricTasteGate_single_carrier_alignment_decode,
      UniformLimitMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformLimitMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformLimitMetricUp
