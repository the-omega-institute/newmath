import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedSetUp : Type where
  | mk (X S c r B H C P N : BHist) : BoundedSetUp
  deriving DecidableEq

def boundedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedSetEncodeBHist h

def boundedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedSetDecodeBHist tail)

private theorem BoundedSetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, boundedSetDecodeBHist (boundedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedSetFields : BoundedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedSetUp.mk X S c r B H C P N => [X, S, c, r, B, H, C, P, N]

def boundedSetToEventFlow : BoundedSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedSetFields x).map boundedSetEncodeBHist

def boundedSetFromEventFlow : EventFlow → Option BoundedSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _S :: [] => none
  | _X :: _S :: _c :: [] => none
  | _X :: _S :: _c :: _r :: [] => none
  | _X :: _S :: _c :: _r :: _B :: [] => none
  | _X :: _S :: _c :: _r :: _B :: _H :: [] => none
  | _X :: _S :: _c :: _r :: _B :: _H :: _C :: [] => none
  | _X :: _S :: _c :: _r :: _B :: _H :: _C :: _P :: [] => none
  | X :: S :: c :: r :: B :: H :: C :: P :: N :: [] =>
      some
        (BoundedSetUp.mk
          (boundedSetDecodeBHist X)
          (boundedSetDecodeBHist S)
          (boundedSetDecodeBHist c)
          (boundedSetDecodeBHist r)
          (boundedSetDecodeBHist B)
          (boundedSetDecodeBHist H)
          (boundedSetDecodeBHist C)
          (boundedSetDecodeBHist P)
          (boundedSetDecodeBHist N))
  | _X :: _S :: _c :: _r :: _B :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem BoundedSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedSetUp, boundedSetFromEventFlow (boundedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S c r B H C P N =>
      change
        some
          (BoundedSetUp.mk
            (boundedSetDecodeBHist (boundedSetEncodeBHist X))
            (boundedSetDecodeBHist (boundedSetEncodeBHist S))
            (boundedSetDecodeBHist (boundedSetEncodeBHist c))
            (boundedSetDecodeBHist (boundedSetEncodeBHist r))
            (boundedSetDecodeBHist (boundedSetEncodeBHist B))
            (boundedSetDecodeBHist (boundedSetEncodeBHist H))
            (boundedSetDecodeBHist (boundedSetEncodeBHist C))
            (boundedSetDecodeBHist (boundedSetEncodeBHist P))
            (boundedSetDecodeBHist (boundedSetEncodeBHist N))) =
          some (BoundedSetUp.mk X S c r B H C P N)
      rw [BoundedSetTasteGate_single_carrier_alignment_decode X,
        BoundedSetTasteGate_single_carrier_alignment_decode S,
        BoundedSetTasteGate_single_carrier_alignment_decode c,
        BoundedSetTasteGate_single_carrier_alignment_decode r,
        BoundedSetTasteGate_single_carrier_alignment_decode B,
        BoundedSetTasteGate_single_carrier_alignment_decode H,
        BoundedSetTasteGate_single_carrier_alignment_decode C,
        BoundedSetTasteGate_single_carrier_alignment_decode P,
        BoundedSetTasteGate_single_carrier_alignment_decode N]

private theorem BoundedSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedSetUp} :
    boundedSetToEventFlow x = boundedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedSetFromEventFlow (boundedSetToEventFlow x) =
        boundedSetFromEventFlow (boundedSetToEventFlow y) :=
    congrArg boundedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedSetTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedSetTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundedSetUp, boundedSetFields x = boundedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 S1 c1 r1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 S2 c2 r2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance boundedSetBHistCarrier : BHistCarrier BoundedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedSetToEventFlow
  fromEventFlow := boundedSetFromEventFlow

instance boundedSetChapterTasteGate : ChapterTasteGate BoundedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedSetFromEventFlow (boundedSetToEventFlow x) = some x
    exact BoundedSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedSetFieldFaithful : FieldFaithful BoundedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedSetFields
  field_faithful := BoundedSetTasteGate_single_carrier_alignment_fields

instance boundedSetNontrivial : Nontrivial BoundedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedSetChapterTasteGate

theorem BoundedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedSetDecodeBHist (boundedSetEncodeBHist h) = h) ∧
      (∀ x : BoundedSetUp,
        boundedSetFromEventFlow (boundedSetToEventFlow x) = some x) ∧
        (∀ x y : BoundedSetUp,
          boundedSetToEventFlow x = boundedSetToEventFlow y → x = y) ∧
          boundedSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BoundedSetTasteGate_single_carrier_alignment_decode,
      BoundedSetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BoundedSetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedSetUp
