import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolishBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolishBasisUp : Type where
  | mk (M D K S R I F H C P N : BHist) : PolishBasisUp
  deriving DecidableEq

def polishBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: polishBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: polishBasisEncodeBHist h

def polishBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (polishBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (polishBasisDecodeBHist tail)

private theorem PolishBasisTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, polishBasisDecodeBHist (polishBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def polishBasisFields : PolishBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PolishBasisUp.mk M D K S R I F H C P N => [M, D, K, S, R, I, F, H, C, P, N]

def polishBasisToEventFlow : PolishBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (polishBasisFields x).map polishBasisEncodeBHist

private def polishBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => polishBasisEventAtDefault index rest

def polishBasisFromEventFlow (ef : EventFlow) : Option PolishBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PolishBasisUp.mk
      (polishBasisDecodeBHist (polishBasisEventAtDefault 0 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 1 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 2 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 3 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 4 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 5 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 6 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 7 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 8 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 9 ef))
      (polishBasisDecodeBHist (polishBasisEventAtDefault 10 ef)))

private theorem PolishBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PolishBasisUp, polishBasisFromEventFlow (polishBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D K S R I F H C P N =>
      change
        some
          (PolishBasisUp.mk
            (polishBasisDecodeBHist (polishBasisEncodeBHist M))
            (polishBasisDecodeBHist (polishBasisEncodeBHist D))
            (polishBasisDecodeBHist (polishBasisEncodeBHist K))
            (polishBasisDecodeBHist (polishBasisEncodeBHist S))
            (polishBasisDecodeBHist (polishBasisEncodeBHist R))
            (polishBasisDecodeBHist (polishBasisEncodeBHist I))
            (polishBasisDecodeBHist (polishBasisEncodeBHist F))
            (polishBasisDecodeBHist (polishBasisEncodeBHist H))
            (polishBasisDecodeBHist (polishBasisEncodeBHist C))
            (polishBasisDecodeBHist (polishBasisEncodeBHist P))
            (polishBasisDecodeBHist (polishBasisEncodeBHist N))) =
          some (PolishBasisUp.mk M D K S R I F H C P N)
      rw [PolishBasisTasteGate_single_carrier_alignment_decode M,
        PolishBasisTasteGate_single_carrier_alignment_decode D,
        PolishBasisTasteGate_single_carrier_alignment_decode K,
        PolishBasisTasteGate_single_carrier_alignment_decode S,
        PolishBasisTasteGate_single_carrier_alignment_decode R,
        PolishBasisTasteGate_single_carrier_alignment_decode I,
        PolishBasisTasteGate_single_carrier_alignment_decode F,
        PolishBasisTasteGate_single_carrier_alignment_decode H,
        PolishBasisTasteGate_single_carrier_alignment_decode C,
        PolishBasisTasteGate_single_carrier_alignment_decode P,
        PolishBasisTasteGate_single_carrier_alignment_decode N]

private theorem PolishBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PolishBasisUp} :
    polishBasisToEventFlow x = polishBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      polishBasisFromEventFlow (polishBasisToEventFlow x) =
        polishBasisFromEventFlow (polishBasisToEventFlow y) :=
    congrArg polishBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PolishBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PolishBasisTasteGate_single_carrier_alignment_round_trip y)))

instance polishBasisBHistCarrier : BHistCarrier PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := polishBasisToEventFlow
  fromEventFlow := polishBasisFromEventFlow

instance polishBasisChapterTasteGate : ChapterTasteGate PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change polishBasisFromEventFlow (polishBasisToEventFlow x) = some x
    exact PolishBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PolishBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance polishBasisFieldFaithful : FieldFaithful PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := polishBasisFields
  field_faithful := by
    intro x y h
    cases x with
    | mk M₁ D₁ K₁ S₁ R₁ I₁ F₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk M₂ D₂ K₂ S₂ R₂ I₂ F₂ H₂ C₂ P₂ N₂ =>
            injection h with hM t1
            injection t1 with hD t2
            injection t2 with hK t3
            injection t3 with hS t4
            injection t4 with hR t5
            injection t5 with hI t6
            injection t6 with hF t7
            injection t7 with hH t8
            injection t8 with hC t9
            injection t9 with hP t10
            injection t10 with hN _
            cases hM
            cases hD
            cases hK
            cases hS
            cases hR
            cases hI
            cases hF
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance polishBasisNontrivial : BEDC.Meta.TasteGate.Nontrivial PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PolishBasisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PolishBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem PolishBasisTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PolishBasisUp) ∧ Nonempty (FieldFaithful PolishBasisUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PolishBasisUp) ∧
        (∀ h : BHist, polishBasisDecodeBHist (polishBasisEncodeBHist h) = h) ∧
          (∀ x : PolishBasisUp, polishBasisFromEventFlow (polishBasisToEventFlow x) = some x) ∧
            (∀ x y : PolishBasisUp, polishBasisToEventFlow x = polishBasisToEventFlow y ->
              x = y) ∧ polishBasisEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨polishBasisChapterTasteGate⟩, ⟨polishBasisFieldFaithful⟩,
      ⟨polishBasisNontrivial⟩, PolishBasisTasteGate_single_carrier_alignment_decode,
      PolishBasisTasteGate_single_carrier_alignment_round_trip,
      (fun x y heq => PolishBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PolishBasisUp
