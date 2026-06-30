import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwartzKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwartzKernelUp : Type where
  | mk (S T U J B R H C P N : BHist) : SchwartzKernelUp
  deriving DecidableEq

def schwartzKernelEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwartzKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwartzKernelEncodeBHist h

def schwartzKernelDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwartzKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwartzKernelDecodeBHist tail)

private theorem SchwartzKernelTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, schwartzKernelDecodeBHist (schwartzKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwartzKernelFields : SchwartzKernelUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | SchwartzKernelUp.mk S T U J B R H C P N => [S, T, U, J, B, R, H, C, P, N]

def schwartzKernelToEventFlow : SchwartzKernelUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | SchwartzKernelUp.mk S T U J B R H C P N =>
      [schwartzKernelEncodeBHist S,
        schwartzKernelEncodeBHist T,
        schwartzKernelEncodeBHist U,
        schwartzKernelEncodeBHist J,
        schwartzKernelEncodeBHist B,
        schwartzKernelEncodeBHist R,
        schwartzKernelEncodeBHist H,
        schwartzKernelEncodeBHist C,
        schwartzKernelEncodeBHist P,
        schwartzKernelEncodeBHist N]

private def schwartzKernelEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schwartzKernelEventAt index rest

def schwartzKernelFromEventFlow : EventFlow → Option SchwartzKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SchwartzKernelUp.mk
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 0 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 1 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 2 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 3 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 4 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 5 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 6 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 7 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 8 ef))
        (schwartzKernelDecodeBHist (schwartzKernelEventAt 9 ef)))

private theorem schwartzKernel_round_trip :
    ∀ x : SchwartzKernelUp,
      schwartzKernelFromEventFlow (schwartzKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T U J B R H C P N =>
      change
        some
            (SchwartzKernelUp.mk
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist S))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist T))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist U))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist J))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist B))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist R))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist H))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist C))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist P))
              (schwartzKernelDecodeBHist (schwartzKernelEncodeBHist N))) =
          some (SchwartzKernelUp.mk S T U J B R H C P N)
      rw [SchwartzKernelTasteGate_single_carrier_alignment_decode S,
        SchwartzKernelTasteGate_single_carrier_alignment_decode T,
        SchwartzKernelTasteGate_single_carrier_alignment_decode U,
        SchwartzKernelTasteGate_single_carrier_alignment_decode J,
        SchwartzKernelTasteGate_single_carrier_alignment_decode B,
        SchwartzKernelTasteGate_single_carrier_alignment_decode R,
        SchwartzKernelTasteGate_single_carrier_alignment_decode H,
        SchwartzKernelTasteGate_single_carrier_alignment_decode C,
        SchwartzKernelTasteGate_single_carrier_alignment_decode P,
        SchwartzKernelTasteGate_single_carrier_alignment_decode N]

private theorem schwartzKernelToEventFlow_injective {x y : SchwartzKernelUp} :
    schwartzKernelToEventFlow x = schwartzKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = schwartzKernelFromEventFlow (schwartzKernelToEventFlow x) :=
        (schwartzKernel_round_trip x).symm
      _ = schwartzKernelFromEventFlow (schwartzKernelToEventFlow y) :=
        congrArg schwartzKernelFromEventFlow hxy
      _ = some y := schwartzKernel_round_trip y
  exact Option.some.inj hsome

private theorem schwartzKernel_field_faithful :
    ∀ x y : SchwartzKernelUp, schwartzKernelFields x = schwartzKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 U1 J1 B1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 U2 J2 B2 R2 H2 C2 P2 N2 =>
          injection hfields with hS tail0
          injection tail0 with hT tail1
          injection tail1 with hU tail2
          injection tail2 with hJ tail3
          injection tail3 with hB tail4
          injection tail4 with hR tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hT
          subst hU
          subst hJ
          subst hB
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance schwartzKernelBHistCarrier : BHistCarrier SchwartzKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwartzKernelToEventFlow
  fromEventFlow := schwartzKernelFromEventFlow

instance schwartzKernelChapterTasteGate : ChapterTasteGate SchwartzKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwartzKernelFromEventFlow (schwartzKernelToEventFlow x) = some x
    exact schwartzKernel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schwartzKernelToEventFlow_injective heq)

instance schwartzKernelFieldFaithful : FieldFaithful SchwartzKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := schwartzKernelFields
  field_faithful := schwartzKernel_field_faithful

instance schwartzKernelNontrivial : Nontrivial SchwartzKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SchwartzKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SchwartzKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SchwartzKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schwartzKernelChapterTasteGate

theorem SchwartzKernelTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SchwartzKernelUp) ∧
      Nonempty (ChapterTasteGate SchwartzKernelUp) ∧
      Nonempty (FieldFaithful SchwartzKernelUp) ∧
      Nonempty SchwartzKernelUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨schwartzKernelBHistCarrier⟩, ⟨schwartzKernelChapterTasteGate⟩,
      ⟨schwartzKernelFieldFaithful⟩,
      ⟨SchwartzKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩⟩

end BEDC.Derived.SchwartzKernelUp
