import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoveringSpacePathLiftingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoveringSpacePathLiftingUp : Type where
  | mk :
      (base cover path lift sheet endpoint transport route provenance nameCert : BHist) →
        CoveringSpacePathLiftingUp
  deriving DecidableEq

def coveringSpacePathLiftingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coveringSpacePathLiftingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coveringSpacePathLiftingEncodeBHist h

def coveringSpacePathLiftingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coveringSpacePathLiftingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coveringSpacePathLiftingDecodeBHist tail)

private theorem coveringSpacePathLifting_decode_encode_bhist :
    ∀ h : BHist,
      coveringSpacePathLiftingDecodeBHist (coveringSpacePathLiftingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def coveringSpacePathLiftingFields : CoveringSpacePathLiftingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CoveringSpacePathLiftingUp.mk base cover path lift sheet endpoint transport route
      provenance nameCert =>
      [base, cover, path, lift, sheet, endpoint, transport, route, provenance, nameCert]

def coveringSpacePathLiftingToEventFlow : CoveringSpacePathLiftingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (coveringSpacePathLiftingFields x).map coveringSpacePathLiftingEncodeBHist

def coveringSpacePathLiftingFromEventFlow :
    EventFlow → Option CoveringSpacePathLiftingUp
  -- BEDC touchpoint anchor: BHist BMark
  | base :: cover :: path :: lift :: sheet :: endpoint :: transport :: route ::
      provenance :: nameCert :: [] =>
      some
        (CoveringSpacePathLiftingUp.mk
          (coveringSpacePathLiftingDecodeBHist base)
          (coveringSpacePathLiftingDecodeBHist cover)
          (coveringSpacePathLiftingDecodeBHist path)
          (coveringSpacePathLiftingDecodeBHist lift)
          (coveringSpacePathLiftingDecodeBHist sheet)
          (coveringSpacePathLiftingDecodeBHist endpoint)
          (coveringSpacePathLiftingDecodeBHist transport)
          (coveringSpacePathLiftingDecodeBHist route)
          (coveringSpacePathLiftingDecodeBHist provenance)
          (coveringSpacePathLiftingDecodeBHist nameCert))
  | _ => none

private theorem coveringSpacePathLifting_round_trip :
    ∀ x : CoveringSpacePathLiftingUp,
      coveringSpacePathLiftingFromEventFlow (coveringSpacePathLiftingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk base cover path lift sheet endpoint transport route provenance nameCert =>
      change
        some
          (CoveringSpacePathLiftingUp.mk
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist base))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist cover))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist path))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist lift))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist sheet))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist endpoint))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist transport))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist route))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist provenance))
            (coveringSpacePathLiftingDecodeBHist
              (coveringSpacePathLiftingEncodeBHist nameCert))) =
          some
            (CoveringSpacePathLiftingUp.mk base cover path lift sheet endpoint
              transport route provenance nameCert)
      rw [coveringSpacePathLifting_decode_encode_bhist base,
        coveringSpacePathLifting_decode_encode_bhist cover,
        coveringSpacePathLifting_decode_encode_bhist path,
        coveringSpacePathLifting_decode_encode_bhist lift,
        coveringSpacePathLifting_decode_encode_bhist sheet,
        coveringSpacePathLifting_decode_encode_bhist endpoint,
        coveringSpacePathLifting_decode_encode_bhist transport,
        coveringSpacePathLifting_decode_encode_bhist route,
        coveringSpacePathLifting_decode_encode_bhist provenance,
        coveringSpacePathLifting_decode_encode_bhist nameCert]

private theorem coveringSpacePathLiftingToEventFlow_injective
    {x y : CoveringSpacePathLiftingUp} :
    coveringSpacePathLiftingToEventFlow x =
      coveringSpacePathLiftingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coveringSpacePathLiftingFromEventFlow (coveringSpacePathLiftingToEventFlow x) =
        coveringSpacePathLiftingFromEventFlow (coveringSpacePathLiftingToEventFlow y) :=
    congrArg coveringSpacePathLiftingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (coveringSpacePathLifting_round_trip x).symm
      (Eq.trans hread (coveringSpacePathLifting_round_trip y)))

instance coveringSpacePathLiftingBHistCarrier :
    BHistCarrier CoveringSpacePathLiftingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coveringSpacePathLiftingToEventFlow
  fromEventFlow := coveringSpacePathLiftingFromEventFlow

instance coveringSpacePathLiftingChapterTasteGate :
    ChapterTasteGate CoveringSpacePathLiftingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      coveringSpacePathLiftingFromEventFlow (coveringSpacePathLiftingToEventFlow x) =
        some x
    exact coveringSpacePathLifting_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (coveringSpacePathLiftingToEventFlow_injective heq)

theorem CoveringSpacePathLiftingTasteGate_single_carrier_alignment :
    (∀ base cover path lift sheet endpoint transport route provenance nameCert : BHist,
      coveringSpacePathLiftingFields
          (CoveringSpacePathLiftingUp.mk base cover path lift sheet endpoint transport
            route provenance nameCert) =
        [base, cover, path, lift, sheet, endpoint, transport, route, provenance,
          nameCert]) ∧
      coveringSpacePathLiftingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro base cover path lift sheet endpoint transport route provenance nameCert
    rfl
  · rfl

end BEDC.Derived.CoveringSpacePathLiftingUp.TasteGate
