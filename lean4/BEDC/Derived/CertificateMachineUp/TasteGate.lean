import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertificateMachineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertificateMachineUp : Type where
  | mk (K O B A R S H C P N : BHist) : CertificateMachineUp
  deriving DecidableEq

def certificateMachineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: certificateMachineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: certificateMachineEncodeBHist h

def certificateMachineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (certificateMachineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (certificateMachineDecodeBHist tail)

private def CertificateMachineTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => CertificateMachineTasteGate_single_carrier_alignment_rawAt n rest

private theorem CertificateMachineTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, certificateMachineDecodeBHist (certificateMachineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def certificateMachineFields : CertificateMachineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CertificateMachineUp.mk K O B A R S H C P N => [K, O, B, A, R, S, H, C, P, N]

def certificateMachineToEventFlow : CertificateMachineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CertificateMachineUp.mk K O B A R S H C P N =>
      [certificateMachineEncodeBHist K,
        certificateMachineEncodeBHist O,
        certificateMachineEncodeBHist B,
        certificateMachineEncodeBHist A,
        certificateMachineEncodeBHist R,
        certificateMachineEncodeBHist S,
        certificateMachineEncodeBHist H,
        certificateMachineEncodeBHist C,
        certificateMachineEncodeBHist P,
        certificateMachineEncodeBHist N]

def certificateMachineFromEventFlow : EventFlow → Option CertificateMachineUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CertificateMachineUp.mk
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 0 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 1 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 2 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 3 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 4 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 5 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 6 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 7 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 8 ef))
          (certificateMachineDecodeBHist
            (CertificateMachineTasteGate_single_carrier_alignment_rawAt 9 ef)))

private theorem CertificateMachineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CertificateMachineUp,
      certificateMachineFromEventFlow (certificateMachineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K O B A R S H C P N =>
      change
        some
          (CertificateMachineUp.mk
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist K))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist O))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist B))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist A))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist R))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist S))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist H))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist C))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist P))
            (certificateMachineDecodeBHist (certificateMachineEncodeBHist N))) =
          some (CertificateMachineUp.mk K O B A R S H C P N)
      rw [CertificateMachineTasteGate_single_carrier_alignment_decode K,
        CertificateMachineTasteGate_single_carrier_alignment_decode O,
        CertificateMachineTasteGate_single_carrier_alignment_decode B,
        CertificateMachineTasteGate_single_carrier_alignment_decode A,
        CertificateMachineTasteGate_single_carrier_alignment_decode R,
        CertificateMachineTasteGate_single_carrier_alignment_decode S,
        CertificateMachineTasteGate_single_carrier_alignment_decode H,
        CertificateMachineTasteGate_single_carrier_alignment_decode C,
        CertificateMachineTasteGate_single_carrier_alignment_decode P,
        CertificateMachineTasteGate_single_carrier_alignment_decode N]

private theorem CertificateMachineTasteGate_single_carrier_alignment_injective
    {x y : CertificateMachineUp} :
    certificateMachineToEventFlow x = certificateMachineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      certificateMachineFromEventFlow (certificateMachineToEventFlow x) =
        certificateMachineFromEventFlow (certificateMachineToEventFlow y) :=
    congrArg certificateMachineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CertificateMachineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CertificateMachineTasteGate_single_carrier_alignment_round_trip y)))

private theorem CertificateMachineTasteGate_single_carrier_alignment_fields :
    ∀ x y : CertificateMachineUp,
      certificateMachineFields x = certificateMachineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ O₁ B₁ A₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ O₂ B₂ A₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance certificateMachineBHistCarrier : BHistCarrier CertificateMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := certificateMachineToEventFlow
  fromEventFlow := certificateMachineFromEventFlow

instance certificateMachineChapterTasteGate :
    ChapterTasteGate CertificateMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change certificateMachineFromEventFlow (certificateMachineToEventFlow x) = some x
    exact CertificateMachineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CertificateMachineTasteGate_single_carrier_alignment_injective heq)

instance certificateMachineFieldFaithful : FieldFaithful CertificateMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := certificateMachineFields
  field_faithful := CertificateMachineTasteGate_single_carrier_alignment_fields

instance certificateMachineNontrivial : Nontrivial CertificateMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CertificateMachineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CertificateMachineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CertificateMachineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  certificateMachineChapterTasteGate

theorem CertificateMachineTasteGate_single_carrier_alignment :
    (∀ h : BHist, certificateMachineDecodeBHist (certificateMachineEncodeBHist h) = h) ∧
      (∀ x : CertificateMachineUp,
        certificateMachineFromEventFlow (certificateMachineToEventFlow x) = some x) ∧
        (∀ x y : CertificateMachineUp,
          certificateMachineToEventFlow x = certificateMachineToEventFlow y → x = y) ∧
          certificateMachineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CertificateMachineTasteGate_single_carrier_alignment_decode,
      ⟨CertificateMachineTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _x _y heq =>
            CertificateMachineTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.CertificateMachineUp
