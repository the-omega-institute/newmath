import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisZeckendorfCannotClaimUp : Type where
  | mk :
      (negative011100 carryRefusal nonnormal boundaryZero fullAxis axisNat dimLift
        route provenance nameRow : BHist) →
      AxisZeckendorfCannotClaimUp
  deriving DecidableEq

def axisZeckendorfCannotClaimEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisZeckendorfCannotClaimEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisZeckendorfCannotClaimEncodeBHist h

def axisZeckendorfCannotClaimDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisZeckendorfCannotClaimDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisZeckendorfCannotClaimDecodeBHist tail)

private theorem axisZeckendorfCannotClaimDecode_encode_bhist :
    ∀ h : BHist,
      axisZeckendorfCannotClaimDecodeBHist (axisZeckendorfCannotClaimEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def axisZeckendorfCannotClaimToEventFlow : AxisZeckendorfCannotClaimUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisZeckendorfCannotClaimUp.mk negative011100 carryRefusal nonnormal boundaryZero
      fullAxis axisNat dimLift route provenance nameRow =>
      [[BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist negative011100,
        [BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist carryRefusal,
        [BMark.b1, BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist nonnormal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist boundaryZero,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist fullAxis,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist axisNat,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist dimLift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axisZeckendorfCannotClaimEncodeBHist nameRow]

private def axisZeckendorfCannotClaimRawAt : Nat → EventFlow → RawEvent
  | _n, [] => []
  | Nat.zero, row :: _tail => row
  | Nat.succ n, _row :: tail => axisZeckendorfCannotClaimRawAt n tail

def axisZeckendorfCannotClaimFromEventFlow :
    EventFlow → Option AxisZeckendorfCannotClaimUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AxisZeckendorfCannotClaimUp.mk
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 1 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 3 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 5 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 7 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 9 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 11 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 13 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 15 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 17 ef))
        (axisZeckendorfCannotClaimDecodeBHist
          (axisZeckendorfCannotClaimRawAt 19 ef)))

private theorem axisZeckendorfCannotClaim_round_trip :
    ∀ x : AxisZeckendorfCannotClaimUp,
      axisZeckendorfCannotClaimFromEventFlow
          (axisZeckendorfCannotClaimToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk negative011100 carryRefusal nonnormal boundaryZero fullAxis axisNat dimLift route
      provenance nameRow =>
      change
        some
          (AxisZeckendorfCannotClaimUp.mk
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist negative011100))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist carryRefusal))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist nonnormal))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist boundaryZero))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist fullAxis))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist axisNat))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist dimLift))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist route))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist provenance))
            (axisZeckendorfCannotClaimDecodeBHist
              (axisZeckendorfCannotClaimEncodeBHist nameRow))) =
          some
            (AxisZeckendorfCannotClaimUp.mk negative011100 carryRefusal nonnormal
              boundaryZero fullAxis axisNat dimLift route provenance nameRow)
      rw [axisZeckendorfCannotClaimDecode_encode_bhist negative011100]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist carryRefusal]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist nonnormal]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist boundaryZero]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist fullAxis]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist axisNat]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist dimLift]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist route]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist provenance]
      rw [axisZeckendorfCannotClaimDecode_encode_bhist nameRow]

instance axisZeckendorfCannotClaimBHistCarrier :
    BHistCarrier AxisZeckendorfCannotClaimUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisZeckendorfCannotClaimToEventFlow
  fromEventFlow := axisZeckendorfCannotClaimFromEventFlow

instance axisZeckendorfCannotClaimChapterTasteGate :
    ChapterTasteGate AxisZeckendorfCannotClaimUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := axisZeckendorfCannotClaim_round_trip
  layer_separation := by
    intro x y hxy flowEq
    apply hxy
    have optionEq :
        axisZeckendorfCannotClaimFromEventFlow (axisZeckendorfCannotClaimToEventFlow x) =
          axisZeckendorfCannotClaimFromEventFlow (axisZeckendorfCannotClaimToEventFlow y) :=
      congrArg axisZeckendorfCannotClaimFromEventFlow flowEq
    rw [axisZeckendorfCannotClaim_round_trip x] at optionEq
    rw [axisZeckendorfCannotClaim_round_trip y] at optionEq
    exact Option.some.inj optionEq

instance axisZeckendorfCannotClaimFieldFaithful :
    FieldFaithful AxisZeckendorfCannotClaimUp where
  fields := fun x =>
    match x with
    | AxisZeckendorfCannotClaimUp.mk negative011100 carryRefusal nonnormal boundaryZero
        fullAxis axisNat dimLift route provenance nameRow =>
        [negative011100, carryRefusal, nonnormal, boundaryZero, fullAxis, axisNat,
          dimLift, route, provenance, nameRow]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk negative011100₁ carryRefusal₁ nonnormal₁ boundaryZero₁ fullAxis₁ axisNat₁
        dimLift₁ route₁ provenance₁ nameRow₁ =>
        cases y with
        | mk negative011100₂ carryRefusal₂ nonnormal₂ boundaryZero₂ fullAxis₂ axisNat₂
            dimLift₂ route₂ provenance₂ nameRow₂ =>
            simp only at h
            injection h with hNegative t1
            injection t1 with hCarry t2
            injection t2 with hNonnormal t3
            injection t3 with hBoundary t4
            injection t4 with hFullAxis t5
            injection t5 with hAxisNat t6
            injection t6 with hDimLift t7
            injection t7 with hRoute t8
            injection t8 with hProvenance t9
            injection t9 with hName _
            subst hNegative
            subst hCarry
            subst hNonnormal
            subst hBoundary
            subst hFullAxis
            subst hAxisNat
            subst hDimLift
            subst hRoute
            subst hProvenance
            subst hName
            rfl

instance axisZeckendorfCannotClaimNontrivial :
    Nontrivial AxisZeckendorfCannotClaimUp where
  witness_pair :=
    ⟨AxisZeckendorfCannotClaimUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisZeckendorfCannotClaimUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisZeckendorfCannotClaimUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisZeckendorfCannotClaimChapterTasteGate

theorem AxisZeckendorfCannotClaimTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      axisZeckendorfCannotClaimDecodeBHist (axisZeckendorfCannotClaimEncodeBHist h) =
        h) ∧
      Nonempty (ChapterTasteGate AxisZeckendorfCannotClaimUp) ∧
        (∀ x : AxisZeckendorfCannotClaimUp,
          ∃ w : RawEvent, List.Mem w (BHistCarrier.toEventFlow x) ∧
            (List.Mem BMark.b0 w ∨ List.Mem BMark.b1 w)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact axisZeckendorfCannotClaimDecode_encode_bhist
  · constructor
    · exact Nonempty.intro inferInstance
    · intro x
      cases x with
      | mk negative011100 carryRefusal nonnormal boundaryZero fullAxis axisNat dimLift
          route provenance nameRow =>
          exact ⟨[BMark.b0], List.Mem.head _, Or.inl (List.Mem.head _)⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp.TasteGate

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.AxisZeckendorfCannotClaimUp :=
  TasteGate.taste_gate

end BEDC.Derived.AxisZeckendorfCannotClaimUp
