import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SturmRootIsolationUp : Type where
  | mk (P I D V B W R S H C Q N : BHist) : SturmRootIsolationUp
  deriving DecidableEq

def sturmRootIsolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sturmRootIsolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sturmRootIsolationEncodeBHist h

def sturmRootIsolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sturmRootIsolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sturmRootIsolationDecodeBHist tail)

private theorem sturmRootIsolationDecode_encode :
    ∀ h : BHist, sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sturmRootIsolationToEventFlow : SturmRootIsolationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SturmRootIsolationUp.mk P I D V B W R S H C Q N =>
      [[BMark.b0],
        sturmRootIsolationEncodeBHist P,
        [BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        sturmRootIsolationEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sturmRootIsolationEncodeBHist N]

private def sturmRootIsolationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sturmRootIsolationEventAtDefault index rest

def sturmRootIsolationFromEventFlow (ef : EventFlow) : Option SturmRootIsolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SturmRootIsolationUp.mk
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 1 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 3 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 5 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 7 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 9 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 11 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 13 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 15 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 17 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 19 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 21 ef))
      (sturmRootIsolationDecodeBHist (sturmRootIsolationEventAtDefault 23 ef)))

private theorem sturmRootIsolation_round_trip :
    ∀ x : SturmRootIsolationUp,
      sturmRootIsolationFromEventFlow (sturmRootIsolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P I D V B W R S H C Q N =>
      change
        some
          (SturmRootIsolationUp.mk
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist P))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist I))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist D))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist V))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist B))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist W))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist R))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist S))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist H))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist C))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist Q))
            (sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist N))) =
          some (SturmRootIsolationUp.mk P I D V B W R S H C Q N)
      rw [sturmRootIsolationDecode_encode P, sturmRootIsolationDecode_encode I,
        sturmRootIsolationDecode_encode D, sturmRootIsolationDecode_encode V,
        sturmRootIsolationDecode_encode B, sturmRootIsolationDecode_encode W,
        sturmRootIsolationDecode_encode R, sturmRootIsolationDecode_encode S,
        sturmRootIsolationDecode_encode H, sturmRootIsolationDecode_encode C,
        sturmRootIsolationDecode_encode Q, sturmRootIsolationDecode_encode N]

private theorem sturmRootIsolationToEventFlow_injective {x y : SturmRootIsolationUp} :
    sturmRootIsolationToEventFlow x = sturmRootIsolationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sturmRootIsolationFromEventFlow (sturmRootIsolationToEventFlow x) =
        sturmRootIsolationFromEventFlow (sturmRootIsolationToEventFlow y) :=
    congrArg sturmRootIsolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sturmRootIsolation_round_trip x).symm
      (Eq.trans hread (sturmRootIsolation_round_trip y)))

def SturmRootIsolationTasteGate_single_carrier_alignment_fields :
    SturmRootIsolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SturmRootIsolationUp.mk P I D V B W R S H C Q N => [P, I, D, V, B, W, R, S, H, C, Q, N]

private theorem sturmRootIsolation_fields_faithful :
    ∀ x y : SturmRootIsolationUp,
      SturmRootIsolationTasteGate_single_carrier_alignment_fields x =
        SturmRootIsolationTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P₁ I₁ D₁ V₁ B₁ W₁ R₁ S₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk P₂ I₂ D₂ V₂ B₂ W₂ R₂ S₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance sturmRootIsolationBHistCarrier : BHistCarrier SturmRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sturmRootIsolationToEventFlow
  fromEventFlow := sturmRootIsolationFromEventFlow

instance sturmRootIsolationChapterTasteGate : ChapterTasteGate SturmRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sturmRootIsolationFromEventFlow (sturmRootIsolationToEventFlow x) = some x
    exact sturmRootIsolation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sturmRootIsolationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SturmRootIsolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sturmRootIsolationChapterTasteGate

instance sturmRootIsolationFieldFaithful : FieldFaithful SturmRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := SturmRootIsolationTasteGate_single_carrier_alignment_fields
  field_faithful := sturmRootIsolation_fields_faithful

instance sturmRootIsolationNontrivial : Nontrivial SturmRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SturmRootIsolationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SturmRootIsolationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SturmRootIsolationTasteGate_single_carrier_alignment :
    (∀ h : BHist, sturmRootIsolationDecodeBHist (sturmRootIsolationEncodeBHist h) = h) ∧
      SturmRootIsolationTasteGate_single_carrier_alignment_fields
          (SturmRootIsolationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨sturmRootIsolationDecode_encode, rfl⟩

end BEDC.Derived.SturmRootIsolationUp
