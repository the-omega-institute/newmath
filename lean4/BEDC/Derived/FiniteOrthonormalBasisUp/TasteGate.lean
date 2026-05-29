import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# FiniteOrthonormalBasisUp TasteGate carrier.
-/

namespace BEDC.Derived.FiniteOrthonormalBasisUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite orthonormal-basis packet with the ten displayed rows. -/
inductive FiniteOrthonormalBasisUp : Type where
  | mk :
      (vectorSpace spanningList gramSchmidt orthogonality coordinateLedger refusal transport
        replay provenance nameCert : BHist) →
      FiniteOrthonormalBasisUp
  deriving DecidableEq

def finiteOrthonormalBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOrthonormalBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOrthonormalBasisEncodeBHist h

def finiteOrthonormalBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOrthonormalBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOrthonormalBasisDecodeBHist tail)

private theorem FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist, finiteOrthonormalBasisDecodeBHist (finiteOrthonormalBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteOrthonormalBasisToEventFlow : FiniteOrthonormalBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOrthonormalBasisUp.mk vectorSpace spanningList gramSchmidt orthogonality
      coordinateLedger refusal transport replay provenance nameCert =>
      [[BMark.b0],
        finiteOrthonormalBasisEncodeBHist vectorSpace,
        [BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist spanningList,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist gramSchmidt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist orthogonality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist coordinateLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteOrthonormalBasisEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteOrthonormalBasisEncodeBHist nameCert]

private def finiteOrthonormalBasisDecodeRows : EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match finiteOrthonormalBasisDecodeRows rest1 with
          | some rows => some (finiteOrthonormalBasisDecodeBHist row :: rows)
          | none => none

private def finiteOrthonormalBasisFromRows :
    List BHist → Option FiniteOrthonormalBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | vectorSpace :: rest0 =>
      match rest0 with
      | [] => none
      | spanningList :: rest1 =>
          match rest1 with
          | [] => none
          | gramSchmidt :: rest2 =>
              match rest2 with
              | [] => none
              | orthogonality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | coordinateLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FiniteOrthonormalBasisUp.mk
                                                  vectorSpace spanningList gramSchmidt
                                                  orthogonality coordinateLedger refusal
                                                  transport replay provenance nameCert)
                                          | _ :: _ => none

def finiteOrthonormalBasisFromEventFlow : EventFlow → Option FiniteOrthonormalBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match finiteOrthonormalBasisDecodeRows ef with
    | some rows => finiteOrthonormalBasisFromRows rows
    | none => none

private theorem FiniteOrthonormalBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteOrthonormalBasisUp,
      finiteOrthonormalBasisFromEventFlow (finiteOrthonormalBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk vectorSpace spanningList gramSchmidt orthogonality coordinateLedger refusal transport
      replay provenance nameCert =>
      change
        some
          (FiniteOrthonormalBasisUp.mk
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist vectorSpace))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist spanningList))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist gramSchmidt))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist orthogonality))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist coordinateLedger))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist refusal))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist transport))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist replay))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist provenance))
            (finiteOrthonormalBasisDecodeBHist
              (finiteOrthonormalBasisEncodeBHist nameCert))) =
          some
            (FiniteOrthonormalBasisUp.mk vectorSpace spanningList gramSchmidt orthogonality
              coordinateLedger refusal transport replay provenance nameCert)
      rw [FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist
          vectorSpace,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist
          spanningList,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist
          gramSchmidt,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist
          orthogonality,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist
          coordinateLedger,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist refusal,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist transport,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist replay,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist provenance,
        FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist nameCert]

private theorem FiniteOrthonormalBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteOrthonormalBasisUp} :
    finiteOrthonormalBasisToEventFlow x = finiteOrthonormalBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOrthonormalBasisFromEventFlow (finiteOrthonormalBasisToEventFlow x) =
        finiteOrthonormalBasisFromEventFlow (finiteOrthonormalBasisToEventFlow y) :=
    congrArg finiteOrthonormalBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteOrthonormalBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteOrthonormalBasisTasteGate_single_carrier_alignment_round_trip y)))

instance finiteOrthonormalBasisBHistCarrier :
    BHistCarrier FiniteOrthonormalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOrthonormalBasisToEventFlow
  fromEventFlow := finiteOrthonormalBasisFromEventFlow

instance finiteOrthonormalBasisChapterTasteGate :
    ChapterTasteGate FiniteOrthonormalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteOrthonormalBasisFromEventFlow (finiteOrthonormalBasisToEventFlow x) = some x
    exact FiniteOrthonormalBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteOrthonormalBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

/-- Public TasteGate object for the finite orthonormal-basis carrier. -/
def taste_gate : ChapterTasteGate FiniteOrthonormalBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteOrthonormalBasisChapterTasteGate

theorem FiniteOrthonormalBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteOrthonormalBasisDecodeBHist (finiteOrthonormalBasisEncodeBHist h) = h) ∧
      (∀ x : FiniteOrthonormalBasisUp,
        finiteOrthonormalBasisFromEventFlow (finiteOrthonormalBasisToEventFlow x) = some x) ∧
      (∀ x y : FiniteOrthonormalBasisUp,
        finiteOrthonormalBasisToEventFlow x = finiteOrthonormalBasisToEventFlow y → x = y) ∧
      finiteOrthonormalBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FiniteOrthonormalBasisTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact FiniteOrthonormalBasisTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FiniteOrthonormalBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteOrthonormalBasisUp
