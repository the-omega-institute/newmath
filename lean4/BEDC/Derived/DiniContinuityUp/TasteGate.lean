import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniContinuityUp : Type where
  | mk (K M L R V U H C P N : BHist) : DiniContinuityUp
  deriving DecidableEq

def diniContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniContinuityEncodeBHist h

def diniContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniContinuityDecodeBHist tail)

private theorem DiniContinuityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, diniContinuityDecodeBHist (diniContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DiniContinuityTasteGate_single_carrier_alignment_fields :
    DiniContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniContinuityUp.mk K M L R V U H C P N => [K, M, L, R, V, U, H, C, P, N]

def diniContinuityToEventFlow : DiniContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiniContinuityUp.mk K M L R V U H C P N =>
      [diniContinuityEncodeBHist K, diniContinuityEncodeBHist M,
        diniContinuityEncodeBHist L, diniContinuityEncodeBHist R,
        diniContinuityEncodeBHist V, diniContinuityEncodeBHist U,
        diniContinuityEncodeBHist H, diniContinuityEncodeBHist C,
        diniContinuityEncodeBHist P, diniContinuityEncodeBHist N]

private def DiniContinuityTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => DiniContinuityTasteGate_single_carrier_alignment_rawAt n rest

private def DiniContinuityTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => DiniContinuityTasteGate_single_carrier_alignment_lengthEq n rest

def diniContinuityFromEventFlow : EventFlow → Option DiniContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match DiniContinuityTasteGate_single_carrier_alignment_lengthEq 10 flow with
      | true =>
          some
            (DiniContinuityUp.mk
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 0 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 1 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 2 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 3 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 4 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 5 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 6 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 7 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 8 flow))
              (diniContinuityDecodeBHist
                (DiniContinuityTasteGate_single_carrier_alignment_rawAt 9 flow)))
      | false => none

private theorem DiniContinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiniContinuityUp,
      diniContinuityFromEventFlow (diniContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M L R V U H C P N =>
      change
        some
          (DiniContinuityUp.mk
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist K))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist M))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist L))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist R))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist V))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist U))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist H))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist C))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist P))
            (diniContinuityDecodeBHist (diniContinuityEncodeBHist N))) =
          some (DiniContinuityUp.mk K M L R V U H C P N)
      rw [DiniContinuityTasteGate_single_carrier_alignment_decode K,
        DiniContinuityTasteGate_single_carrier_alignment_decode M,
        DiniContinuityTasteGate_single_carrier_alignment_decode L,
        DiniContinuityTasteGate_single_carrier_alignment_decode R,
        DiniContinuityTasteGate_single_carrier_alignment_decode V,
        DiniContinuityTasteGate_single_carrier_alignment_decode U,
        DiniContinuityTasteGate_single_carrier_alignment_decode H,
        DiniContinuityTasteGate_single_carrier_alignment_decode C,
        DiniContinuityTasteGate_single_carrier_alignment_decode P,
        DiniContinuityTasteGate_single_carrier_alignment_decode N]

private theorem DiniContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiniContinuityUp} :
    diniContinuityToEventFlow x = diniContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniContinuityFromEventFlow (diniContinuityToEventFlow x) =
        diniContinuityFromEventFlow (diniContinuityToEventFlow y) :=
    congrArg diniContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiniContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiniContinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiniContinuityTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DiniContinuityUp,
      DiniContinuityTasteGate_single_carrier_alignment_fields x =
          DiniContinuityTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ M₁ L₁ R₁ V₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ M₂ L₂ R₂ V₂ U₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hM tail1
          injection tail1 with hL tail2
          injection tail2 with hR tail3
          injection tail3 with hV tail4
          injection tail4 with hU tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hK
          subst hM
          subst hL
          subst hR
          subst hV
          subst hU
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance diniContinuityBHistCarrier : BHistCarrier DiniContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniContinuityToEventFlow
  fromEventFlow := diniContinuityFromEventFlow

instance diniContinuityChapterTasteGate : ChapterTasteGate DiniContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diniContinuityFromEventFlow (diniContinuityToEventFlow x) = some x
    exact DiniContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiniContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance diniContinuityFieldFaithful : FieldFaithful DiniContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DiniContinuityTasteGate_single_carrier_alignment_fields
  field_faithful := DiniContinuityTasteGate_single_carrier_alignment_fields_faithful

instance diniContinuityNontrivial : Nontrivial DiniContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiniContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiniContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DiniContinuityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DiniContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diniContinuityChapterTasteGate

theorem DiniContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist, diniContinuityDecodeBHist (diniContinuityEncodeBHist h) = h) ∧
      (∀ x : DiniContinuityUp,
        diniContinuityFromEventFlow (diniContinuityToEventFlow x) = some x) ∧
      (∀ x y : DiniContinuityUp,
        diniContinuityToEventFlow x = diniContinuityToEventFlow y → x = y) ∧
      diniContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DiniContinuityTasteGate_single_carrier_alignment_decode,
      DiniContinuityTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        DiniContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DiniContinuityUp
