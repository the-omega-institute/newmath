import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICProofObjectAuditRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICProofObjectAuditRouteUp : Type where
  | mk (S O D N C B H R P L : BHist) : MetaCICProofObjectAuditRouteUp
  deriving DecidableEq

def metaCICProofObjectAuditRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICProofObjectAuditRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICProofObjectAuditRouteEncodeBHist h

def metaCICProofObjectAuditRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICProofObjectAuditRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICProofObjectAuditRouteDecodeBHist tail)

private theorem metaCICProofObjectAuditRouteDecode_encode_bhist :
    ∀ h : BHist,
      metaCICProofObjectAuditRouteDecodeBHist
        (metaCICProofObjectAuditRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICProofObjectAuditRouteFields :
    MetaCICProofObjectAuditRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L =>
      [S, O, D, N, C, B, H, R, P, L]

def metaCICProofObjectAuditRouteToEventFlow :
    MetaCICProofObjectAuditRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICProofObjectAuditRouteFields x).map
      metaCICProofObjectAuditRouteEncodeBHist

def metaCICProofObjectAuditRouteFromEventFlow :
    EventFlow → Option MetaCICProofObjectAuditRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | S :: O :: D :: N :: C :: B :: H :: R :: P :: L :: [] =>
      some
        (MetaCICProofObjectAuditRouteUp.mk
          (metaCICProofObjectAuditRouteDecodeBHist S)
          (metaCICProofObjectAuditRouteDecodeBHist O)
          (metaCICProofObjectAuditRouteDecodeBHist D)
          (metaCICProofObjectAuditRouteDecodeBHist N)
          (metaCICProofObjectAuditRouteDecodeBHist C)
          (metaCICProofObjectAuditRouteDecodeBHist B)
          (metaCICProofObjectAuditRouteDecodeBHist H)
          (metaCICProofObjectAuditRouteDecodeBHist R)
          (metaCICProofObjectAuditRouteDecodeBHist P)
          (metaCICProofObjectAuditRouteDecodeBHist L))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k ::
      _rest => none

private theorem metaCICProofObjectAuditRoute_round_trip :
    ∀ x : MetaCICProofObjectAuditRouteUp,
      metaCICProofObjectAuditRouteFromEventFlow
        (metaCICProofObjectAuditRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S O D N C B H R P L =>
      change
        some
          (MetaCICProofObjectAuditRouteUp.mk
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist S))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist O))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist D))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist N))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist C))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist B))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist H))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist R))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist P))
            (metaCICProofObjectAuditRouteDecodeBHist
              (metaCICProofObjectAuditRouteEncodeBHist L))) =
          some (MetaCICProofObjectAuditRouteUp.mk S O D N C B H R P L)
      rw [metaCICProofObjectAuditRouteDecode_encode_bhist S,
        metaCICProofObjectAuditRouteDecode_encode_bhist O,
        metaCICProofObjectAuditRouteDecode_encode_bhist D,
        metaCICProofObjectAuditRouteDecode_encode_bhist N,
        metaCICProofObjectAuditRouteDecode_encode_bhist C,
        metaCICProofObjectAuditRouteDecode_encode_bhist B,
        metaCICProofObjectAuditRouteDecode_encode_bhist H,
        metaCICProofObjectAuditRouteDecode_encode_bhist R,
        metaCICProofObjectAuditRouteDecode_encode_bhist P,
        metaCICProofObjectAuditRouteDecode_encode_bhist L]

private theorem metaCICProofObjectAuditRouteToEventFlow_injective
    {x y : MetaCICProofObjectAuditRouteUp} :
    metaCICProofObjectAuditRouteToEventFlow x =
      metaCICProofObjectAuditRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICProofObjectAuditRouteFromEventFlow
          (metaCICProofObjectAuditRouteToEventFlow x) =
        metaCICProofObjectAuditRouteFromEventFlow
          (metaCICProofObjectAuditRouteToEventFlow y) :=
    congrArg metaCICProofObjectAuditRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICProofObjectAuditRoute_round_trip x).symm
      (Eq.trans hread (metaCICProofObjectAuditRoute_round_trip y)))

private theorem metaCICProofObjectAuditRoute_fields_faithful :
    ∀ x y : MetaCICProofObjectAuditRouteUp,
      metaCICProofObjectAuditRouteFields x =
        metaCICProofObjectAuditRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S O D N C B H R P L =>
      cases y with
      | mk S' O' D' N' C' B' H' R' P' L' =>
          cases hfields
          rfl

instance metaCICProofObjectAuditRouteBHistCarrier :
    BHistCarrier MetaCICProofObjectAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICProofObjectAuditRouteToEventFlow
  fromEventFlow := metaCICProofObjectAuditRouteFromEventFlow

instance metaCICProofObjectAuditRouteChapterTasteGate :
    ChapterTasteGate MetaCICProofObjectAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICProofObjectAuditRouteFromEventFlow
        (metaCICProofObjectAuditRouteToEventFlow x) = some x
    exact metaCICProofObjectAuditRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICProofObjectAuditRouteToEventFlow_injective heq)

instance metaCICProofObjectAuditRouteFieldFaithful :
    FieldFaithful MetaCICProofObjectAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICProofObjectAuditRouteFields
  field_faithful := metaCICProofObjectAuditRoute_fields_faithful

instance metaCICProofObjectAuditRouteNontrivial :
    Nontrivial MetaCICProofObjectAuditRouteUp where
  witness_pair :=
    ⟨MetaCICProofObjectAuditRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICProofObjectAuditRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICProofObjectAuditRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICProofObjectAuditRouteChapterTasteGate

theorem MetaCICProofObjectAuditRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metaCICProofObjectAuditRouteDecodeBHist
          (metaCICProofObjectAuditRouteEncodeBHist h) = h) ∧
      (∀ x : MetaCICProofObjectAuditRouteUp,
        metaCICProofObjectAuditRouteFromEventFlow
          (metaCICProofObjectAuditRouteToEventFlow x) = some x) ∧
      (∀ x y : MetaCICProofObjectAuditRouteUp,
        metaCICProofObjectAuditRouteToEventFlow x =
          metaCICProofObjectAuditRouteToEventFlow y → x = y) ∧
      metaCICProofObjectAuditRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨metaCICProofObjectAuditRouteDecode_encode_bhist,
    metaCICProofObjectAuditRoute_round_trip,
    fun _ _ heq => metaCICProofObjectAuditRouteToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.MetaCICProofObjectAuditRouteUp
