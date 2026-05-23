import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HolderContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HolderContinuityUp : Type where
  | mk (X Y G alpha K M H C P N : BHist) : HolderContinuityUp
  deriving DecidableEq

def holderContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: holderContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: holderContinuityEncodeBHist h

def holderContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (holderContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (holderContinuityDecodeBHist tail)

private theorem holderContinuityDecode_encode :
    ∀ h : BHist, holderContinuityDecodeBHist (holderContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def holderContinuityToEventFlow : HolderContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HolderContinuityUp.mk X Y G alpha K M H C P N =>
      [holderContinuityEncodeBHist X,
        holderContinuityEncodeBHist Y,
        holderContinuityEncodeBHist G,
        holderContinuityEncodeBHist alpha,
        holderContinuityEncodeBHist K,
        holderContinuityEncodeBHist M,
        holderContinuityEncodeBHist H,
        holderContinuityEncodeBHist C,
        holderContinuityEncodeBHist P,
        holderContinuityEncodeBHist N]

def holderContinuityFromEventFlow : EventFlow → Option HolderContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest =>
      match rest with
      | [] => none
      | Y :: rest =>
          match rest with
          | [] => none
          | G :: rest =>
              match rest with
              | [] => none
              | alpha :: rest =>
                  match rest with
                  | [] => none
                  | K :: rest =>
                      match rest with
                      | [] => none
                      | M :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (HolderContinuityUp.mk
                                                  (holderContinuityDecodeBHist X)
                                                  (holderContinuityDecodeBHist Y)
                                                  (holderContinuityDecodeBHist G)
                                                  (holderContinuityDecodeBHist alpha)
                                                  (holderContinuityDecodeBHist K)
                                                  (holderContinuityDecodeBHist M)
                                                  (holderContinuityDecodeBHist H)
                                                  (holderContinuityDecodeBHist C)
                                                  (holderContinuityDecodeBHist P)
                                                  (holderContinuityDecodeBHist N))
                                          | _ :: _ => none

private theorem holderContinuity_round_trip :
    ∀ x : HolderContinuityUp,
      holderContinuityFromEventFlow (holderContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y G alpha K M H C P N =>
      rw [holderContinuityToEventFlow, holderContinuityFromEventFlow,
        holderContinuityDecode_encode X,
        holderContinuityDecode_encode Y,
        holderContinuityDecode_encode G,
        holderContinuityDecode_encode alpha,
        holderContinuityDecode_encode K,
        holderContinuityDecode_encode M,
        holderContinuityDecode_encode H,
        holderContinuityDecode_encode C,
        holderContinuityDecode_encode P,
        holderContinuityDecode_encode N]

private theorem holderContinuityToEventFlow_injective {x y : HolderContinuityUp} :
    holderContinuityToEventFlow x = holderContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      holderContinuityFromEventFlow (holderContinuityToEventFlow x) =
        holderContinuityFromEventFlow (holderContinuityToEventFlow y) :=
    congrArg holderContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (holderContinuity_round_trip x).symm
      (Eq.trans hread (holderContinuity_round_trip y)))

def holderContinuityFields : HolderContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HolderContinuityUp.mk X Y G alpha K M H C P N => [X, Y, G, alpha, K, M, H, C, P, N]

private theorem holderContinuity_field_faithful :
    ∀ x y : HolderContinuityUp, holderContinuityFields x = holderContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 G1 alpha1 K1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 G2 alpha2 K2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance holderContinuityBHistCarrier : BHistCarrier HolderContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := holderContinuityToEventFlow
  fromEventFlow := holderContinuityFromEventFlow

instance holderContinuityChapterTasteGate : ChapterTasteGate HolderContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change holderContinuityFromEventFlow (holderContinuityToEventFlow x) = some x
    exact holderContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (holderContinuityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HolderContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  holderContinuityChapterTasteGate

instance holderContinuityFieldFaithful : FieldFaithful HolderContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := holderContinuityFields
  field_faithful := holderContinuity_field_faithful

instance holderContinuityNontrivial : Nontrivial HolderContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HolderContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HolderContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HolderContinuityUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, holderContinuityDecodeBHist (holderContinuityEncodeBHist h) = h) ∧
      (∀ x : HolderContinuityUp,
        holderContinuityFromEventFlow (holderContinuityToEventFlow x) = some x) ∧
      (∀ x y : HolderContinuityUp,
        holderContinuityToEventFlow x = holderContinuityToEventFlow y → x = y) ∧
      holderContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨holderContinuityDecode_encode,
      holderContinuity_round_trip,
      fun _ _ heq => holderContinuityToEventFlow_injective heq,
      rfl⟩

theorem HolderContinuityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HolderContinuityUp) ∧
      Nonempty (FieldFaithful HolderContinuityUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial HolderContinuityUp) ∧
      (∀ h : BHist, holderContinuityDecodeBHist (holderContinuityEncodeBHist h) = h) ∧
      (∀ x : HolderContinuityUp,
        holderContinuityFromEventFlow (holderContinuityToEventFlow x) = some x) ∧
      (∀ x y : HolderContinuityUp,
        holderContinuityToEventFlow x = holderContinuityToEventFlow y → x = y) ∧
      holderContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro holderContinuityChapterTasteGate,
      Nonempty.intro holderContinuityFieldFaithful,
      Nonempty.intro holderContinuityNontrivial,
      holderContinuityDecode_encode,
      holderContinuity_round_trip,
      fun _ _ heq => holderContinuityToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.HolderContinuityUp
