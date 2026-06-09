import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformFixedPointUp : Type where
  | mk (M F I Q U0 E H C P N : BHist) : UniformFixedPointUp
  deriving DecidableEq

def uniformFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformFixedPointEncodeBHist h

def uniformFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformFixedPointDecodeBHist tail)

private theorem UniformFixedPointTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformFixedPointFields : UniformFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformFixedPointUp.mk M F I Q U0 E H C P N => [M, F, I, Q, U0, E, H, C, P, N]

def uniformFixedPointToEventFlow : UniformFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformFixedPointFields x).map uniformFixedPointEncodeBHist

def uniformFixedPointFromEventFlow : EventFlow → Option UniformFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: restF =>
      match restF with
      | [] => none
      | F :: restI =>
          match restI with
          | [] => none
          | I :: restQ =>
              match restQ with
              | [] => none
              | Q :: restU0 =>
                  match restU0 with
                  | [] => none
                  | U0 :: restE =>
                      match restE with
                      | [] => none
                      | E :: restH =>
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
                                                (UniformFixedPointUp.mk
                                                  (uniformFixedPointDecodeBHist M)
                                                  (uniformFixedPointDecodeBHist F)
                                                  (uniformFixedPointDecodeBHist I)
                                                  (uniformFixedPointDecodeBHist Q)
                                                  (uniformFixedPointDecodeBHist U0)
                                                  (uniformFixedPointDecodeBHist E)
                                                  (uniformFixedPointDecodeBHist H)
                                                  (uniformFixedPointDecodeBHist C)
                                                  (uniformFixedPointDecodeBHist P)
                                                  (uniformFixedPointDecodeBHist N))
                                          | _ :: _ => none

private theorem UniformFixedPointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformFixedPointUp,
      uniformFixedPointFromEventFlow (uniformFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F I Q U0 E H C P N =>
      change
        some
          (UniformFixedPointUp.mk
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist M))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist F))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist I))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist Q))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist U0))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist E))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist H))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist C))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist P))
            (uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist N))) =
          some (UniformFixedPointUp.mk M F I Q U0 E H C P N)
      rw [UniformFixedPointTasteGate_single_carrier_alignment_decode_encode M,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode F,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode I,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode Q,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode U0,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode E,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode H,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode C,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode P,
        UniformFixedPointTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformFixedPointUp} :
    uniformFixedPointToEventFlow x = uniformFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformFixedPointFromEventFlow (uniformFixedPointToEventFlow x) =
        uniformFixedPointFromEventFlow (uniformFixedPointToEventFlow y) :=
    congrArg uniformFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformFixedPointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformFixedPointTasteGate_single_carrier_alignment_round_trip y)))

instance uniformFixedPointBHistCarrier : BHistCarrier UniformFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformFixedPointToEventFlow
  fromEventFlow := uniformFixedPointFromEventFlow

instance uniformFixedPointChapterTasteGate : ChapterTasteGate UniformFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformFixedPointFromEventFlow (uniformFixedPointToEventFlow x) = some x
    exact UniformFixedPointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformFixedPointDecodeBHist (uniformFixedPointEncodeBHist h) = h) ∧
      (∀ x : UniformFixedPointUp,
        uniformFixedPointFromEventFlow (uniformFixedPointToEventFlow x) = some x) ∧
      (∀ x y : UniformFixedPointUp,
        uniformFixedPointToEventFlow x = uniformFixedPointToEventFlow y → x = y) ∧
      uniformFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformFixedPointTasteGate_single_carrier_alignment_decode_encode,
      UniformFixedPointTasteGate_single_carrier_alignment_round_trip,
      fun x y heq => UniformFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.UniformFixedPointUp
