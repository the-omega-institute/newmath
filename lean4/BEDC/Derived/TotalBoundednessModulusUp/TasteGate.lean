import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotalBoundednessModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotalBoundednessModulusUp : Type where
  | mk (M N D R E H C P L : BHist) : TotalBoundednessModulusUp
  deriving DecidableEq

def totalBoundednessModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totalBoundednessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totalBoundednessModulusEncodeBHist h

def totalBoundednessModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totalBoundednessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totalBoundednessModulusDecodeBHist tail)

private theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totalBoundednessModulusToEventFlow : TotalBoundednessModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotalBoundednessModulusUp.mk M N D R E H C P L =>
      [[BMark.b0],
        totalBoundednessModulusEncodeBHist M,
        [BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        totalBoundednessModulusEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        totalBoundednessModulusEncodeBHist L]

def totalBoundednessModulusFromEventFlow : EventFlow → Option TotalBoundednessModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b0], M, [BMark.b1, BMark.b0], N, [BMark.b1, BMark.b1, BMark.b0], D,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b0], R,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], E,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], H,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], C,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b0], P,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b0], L] =>
      some
        (TotalBoundednessModulusUp.mk
          (totalBoundednessModulusDecodeBHist M)
          (totalBoundednessModulusDecodeBHist N)
          (totalBoundednessModulusDecodeBHist D)
          (totalBoundednessModulusDecodeBHist R)
          (totalBoundednessModulusDecodeBHist E)
          (totalBoundednessModulusDecodeBHist H)
          (totalBoundednessModulusDecodeBHist C)
          (totalBoundednessModulusDecodeBHist P)
          (totalBoundednessModulusDecodeBHist L))
  | _ => none

private theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TotalBoundednessModulusUp,
      totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M N D R E H C P L =>
      change
        some
          (TotalBoundednessModulusUp.mk
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist M))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist N))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist D))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist R))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist E))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist H))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist C))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist P))
            (totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist L))) =
          some (TotalBoundednessModulusUp.mk M N D R E H C P L)
      rw [TotalBoundednessModulusTasteGate_single_carrier_alignment_decode M,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode N,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode D,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode R,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode E,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode H,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode C,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode P,
        TotalBoundednessModulusTasteGate_single_carrier_alignment_decode L]

private theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_injective
    {x y : TotalBoundednessModulusUp} :
    totalBoundednessModulusToEventFlow x = totalBoundednessModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) =
        totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow y) :=
    congrArg totalBoundednessModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip y)))

private def totalBoundednessModulusFields : TotalBoundednessModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotalBoundednessModulusUp.mk M N D R E H C P L => [M, N, D, R, E, H, C, P, L]

private theorem TotalBoundednessModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : TotalBoundednessModulusUp,
      totalBoundednessModulusFields x = totalBoundednessModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 N1 D1 R1 E1 H1 C1 P1 L1 =>
      cases y with
      | mk M2 N2 D2 R2 E2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance totalBoundednessModulusBHistCarrier : BHistCarrier TotalBoundednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totalBoundednessModulusToEventFlow
  fromEventFlow := totalBoundednessModulusFromEventFlow

instance totalBoundednessModulusChapterTasteGate :
    ChapterTasteGate TotalBoundednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) =
        some x
    exact TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TotalBoundednessModulusTasteGate_single_carrier_alignment_injective heq)

instance totalBoundednessModulusFieldFaithful :
    FieldFaithful TotalBoundednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := totalBoundednessModulusFields
  field_faithful := TotalBoundednessModulusTasteGate_single_carrier_alignment_fields

instance totalBoundednessModulusNontrivial : Nontrivial TotalBoundednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TotalBoundednessModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TotalBoundednessModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TotalBoundednessModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      totalBoundednessModulusDecodeBHist (totalBoundednessModulusEncodeBHist h) = h) ∧
      (∀ x : TotalBoundednessModulusUp,
        totalBoundednessModulusFromEventFlow (totalBoundednessModulusToEventFlow x) =
          some x) ∧
        (∀ x y : TotalBoundednessModulusUp,
          totalBoundednessModulusToEventFlow x = totalBoundednessModulusToEventFlow y →
            x = y) ∧
          Nonempty (ChapterTasteGate TotalBoundednessModulusUp) ∧
            Nonempty (FieldFaithful TotalBoundednessModulusUp) ∧
              Nonempty (Nontrivial TotalBoundednessModulusUp) ∧
                totalBoundednessModulusEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TotalBoundednessModulusTasteGate_single_carrier_alignment_decode
  constructor
  · exact TotalBoundednessModulusTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact TotalBoundednessModulusTasteGate_single_carrier_alignment_injective heq
  constructor
  · exact ⟨totalBoundednessModulusChapterTasteGate⟩
  constructor
  · exact ⟨totalBoundednessModulusFieldFaithful⟩
  constructor
  · exact ⟨totalBoundednessModulusNontrivial⟩
  · rfl

end BEDC.Derived.TotalBoundednessModulusUp.TasteGate
