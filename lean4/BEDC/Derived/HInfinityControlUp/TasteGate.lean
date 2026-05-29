import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# HInfinityControlUp TasteGate carrier.
-/

namespace BEDC.Derived.HInfinityControlUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite bounded-gain robust-control packet with the thirteen displayed rows. -/
inductive HInfinityControlUp : Type where
  | mk :
      (stateSpace disturbanceInput performanceOutput controller gainBound finiteRollout
        riccatiDependency lqrDependency predictiveDependency transport replay provenance
        nameCert : BHist) →
      HInfinityControlUp
  deriving DecidableEq

def hInfinityControlEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hInfinityControlEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hInfinityControlEncodeBHist h

def hInfinityControlDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hInfinityControlDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hInfinityControlDecodeBHist tail)

private theorem HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist, hInfinityControlDecodeBHist (hInfinityControlEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hInfinityControlToEventFlow : HInfinityControlUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HInfinityControlUp.mk stateSpace disturbanceInput performanceOutput controller gainBound
      finiteRollout riccatiDependency lqrDependency predictiveDependency transport replay
      provenance nameCert =>
      [[BMark.b0],
        hInfinityControlEncodeBHist stateSpace,
        [BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist disturbanceInput,
        [BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist performanceOutput,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist controller,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist gainBound,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist finiteRollout,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist riccatiDependency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hInfinityControlEncodeBHist lqrDependency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist predictiveDependency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hInfinityControlEncodeBHist nameCert]

private def hInfinityControlDecodeRows : EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match hInfinityControlDecodeRows rest1 with
          | some rows => some (hInfinityControlDecodeBHist row :: rows)
          | none => none

private def hInfinityControlFromRows : List BHist → Option HInfinityControlUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | stateSpace :: rest0 =>
      match rest0 with
      | [] => none
      | disturbanceInput :: rest1 =>
          match rest1 with
          | [] => none
          | performanceOutput :: rest2 =>
              match rest2 with
              | [] => none
              | controller :: rest3 =>
                  match rest3 with
                  | [] => none
                  | gainBound :: rest4 =>
                      match rest4 with
                      | [] => none
                      | finiteRollout :: rest5 =>
                          match rest5 with
                          | [] => none
                          | riccatiDependency :: rest6 =>
                              match rest6 with
                              | [] => none
                              | lqrDependency :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | predictiveDependency :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | replay :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | nameCert :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (HInfinityControlUp.mk
                                                              stateSpace disturbanceInput
                                                              performanceOutput controller
                                                              gainBound finiteRollout
                                                              riccatiDependency lqrDependency
                                                              predictiveDependency transport
                                                              replay provenance nameCert)
                                                      | _ :: _ => none

def hInfinityControlFromEventFlow : EventFlow → Option HInfinityControlUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match hInfinityControlDecodeRows ef with
    | some rows => hInfinityControlFromRows rows
    | none => none

private theorem HInfinityControlTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HInfinityControlUp,
      hInfinityControlFromEventFlow (hInfinityControlToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stateSpace disturbanceInput performanceOutput controller gainBound finiteRollout
      riccatiDependency lqrDependency predictiveDependency transport replay provenance nameCert =>
      change
        some
          (HInfinityControlUp.mk
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist stateSpace))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist disturbanceInput))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist performanceOutput))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist controller))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist gainBound))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist finiteRollout))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist riccatiDependency))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist lqrDependency))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist predictiveDependency))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist transport))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist replay))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist provenance))
            (hInfinityControlDecodeBHist (hInfinityControlEncodeBHist nameCert))) =
          some
            (HInfinityControlUp.mk stateSpace disturbanceInput performanceOutput controller
              gainBound finiteRollout riccatiDependency lqrDependency predictiveDependency
              transport replay provenance nameCert)
      rw [HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist stateSpace,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist disturbanceInput,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist performanceOutput,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist controller,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist gainBound,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist finiteRollout,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist riccatiDependency,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist lqrDependency,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist predictiveDependency,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist transport,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist replay,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist provenance,
        HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist nameCert]

private theorem HInfinityControlTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HInfinityControlUp} :
    hInfinityControlToEventFlow x = hInfinityControlToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hInfinityControlFromEventFlow (hInfinityControlToEventFlow x) =
        hInfinityControlFromEventFlow (hInfinityControlToEventFlow y) :=
    congrArg hInfinityControlFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HInfinityControlTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HInfinityControlTasteGate_single_carrier_alignment_round_trip y)))

instance hInfinityControlBHistCarrier : BHistCarrier HInfinityControlUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hInfinityControlToEventFlow
  fromEventFlow := hInfinityControlFromEventFlow

instance hInfinityControlChapterTasteGate : ChapterTasteGate HInfinityControlUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hInfinityControlFromEventFlow (hInfinityControlToEventFlow x) = some x
    exact HInfinityControlTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HInfinityControlTasteGate_single_carrier_alignment_toEventFlow_injective heq)

/-- Public TasteGate object for the finite robust-control carrier. -/
def taste_gate : ChapterTasteGate HInfinityControlUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hInfinityControlChapterTasteGate

theorem HInfinityControlTasteGate_single_carrier_alignment :
    (∀ h : BHist, hInfinityControlDecodeBHist (hInfinityControlEncodeBHist h) = h) ∧
      (∀ x : HInfinityControlUp,
        hInfinityControlFromEventFlow (hInfinityControlToEventFlow x) = some x) ∧
      (∀ x y : HInfinityControlUp,
        hInfinityControlToEventFlow x = hInfinityControlToEventFlow y → x = y) ∧
      hInfinityControlEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HInfinityControlTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact HInfinityControlTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HInfinityControlTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.HInfinityControlUp
