import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofObligationGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofObligationGapUp : Type where
  | mk (O B R M H C P N : BHist) : ProofObligationGapUp
  deriving DecidableEq

def proofObligationGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofObligationGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofObligationGapEncodeBHist h

def proofObligationGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofObligationGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofObligationGapDecodeBHist tail)

private theorem ProofObligationGapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, proofObligationGapDecodeBHist
      (proofObligationGapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def proofObligationGapFields : ProofObligationGapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProofObligationGapUp.mk O B R M H C P N => [O, B, R, M, H, C, P, N]

def proofObligationGapToEventFlow : ProofObligationGapUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (proofObligationGapFields x).map proofObligationGapEncodeBHist

private def proofObligationGapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => proofObligationGapEventAtDefault index rest

def proofObligationGapFromEventFlow
    (ef : EventFlow) : Option ProofObligationGapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProofObligationGapUp.mk
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 0 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 1 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 2 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 3 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 4 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 5 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 6 ef))
      (proofObligationGapDecodeBHist (proofObligationGapEventAtDefault 7 ef)))

private theorem ProofObligationGapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProofObligationGapUp,
      proofObligationGapFromEventFlow
        (proofObligationGapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk O B R M H C P N =>
      change
        some
          (ProofObligationGapUp.mk
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist O))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist B))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist R))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist M))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist H))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist C))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist P))
            (proofObligationGapDecodeBHist (proofObligationGapEncodeBHist N))) =
          some (ProofObligationGapUp.mk O B R M H C P N)
      rw [ProofObligationGapTasteGate_single_carrier_alignment_decode O,
        ProofObligationGapTasteGate_single_carrier_alignment_decode B,
        ProofObligationGapTasteGate_single_carrier_alignment_decode R,
        ProofObligationGapTasteGate_single_carrier_alignment_decode M,
        ProofObligationGapTasteGate_single_carrier_alignment_decode H,
        ProofObligationGapTasteGate_single_carrier_alignment_decode C,
        ProofObligationGapTasteGate_single_carrier_alignment_decode P,
        ProofObligationGapTasteGate_single_carrier_alignment_decode N]

private theorem ProofObligationGapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProofObligationGapUp} :
    proofObligationGapToEventFlow x = proofObligationGapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofObligationGapFromEventFlow (proofObligationGapToEventFlow x) =
        proofObligationGapFromEventFlow (proofObligationGapToEventFlow y) :=
    congrArg proofObligationGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProofObligationGapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ProofObligationGapTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProofObligationGapTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProofObligationGapUp,
      proofObligationGapFields x = proofObligationGapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 B1 R1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 B2 R2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance proofObligationGapBHistCarrier : BHistCarrier ProofObligationGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofObligationGapToEventFlow
  fromEventFlow := proofObligationGapFromEventFlow

instance proofObligationGapChapterTasteGate :
    ChapterTasteGate ProofObligationGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proofObligationGapFromEventFlow (proofObligationGapToEventFlow x) = some x
    exact ProofObligationGapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProofObligationGapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance proofObligationGapFieldFaithful :
    FieldFaithful ProofObligationGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := proofObligationGapFields
  field_faithful := ProofObligationGapTasteGate_single_carrier_alignment_fields

instance proofObligationGapNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ProofObligationGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProofObligationGapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ProofObligationGapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProofObligationGapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proofObligationGapChapterTasteGate

theorem ProofObligationGapTasteGate_single_carrier_alignment :
    (∀ h : BHist, proofObligationGapDecodeBHist (proofObligationGapEncodeBHist h) = h) ∧
      (∀ x : ProofObligationGapUp,
        proofObligationGapFromEventFlow (proofObligationGapToEventFlow x) = some x) ∧
        (∀ x y : ProofObligationGapUp,
          proofObligationGapToEventFlow x = proofObligationGapToEventFlow y → x = y) ∧
          proofObligationGapEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            proofObligationGapEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ProofObligationGapTasteGate_single_carrier_alignment_decode,
      ProofObligationGapTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ProofObligationGapTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      rfl⟩

end BEDC.Derived.ProofObligationGapUp
