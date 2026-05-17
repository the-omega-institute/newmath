import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpgradeRegistryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpgradeRegistryUp : Type where
  | mk (T S Nx F B A R H C P L : BHist) : UpgradeRegistryUp
  deriving DecidableEq

def upgradeRegistryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upgradeRegistryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upgradeRegistryEncodeBHist h

def upgradeRegistryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upgradeRegistryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upgradeRegistryDecodeBHist tail)

private theorem upgradeRegistryDecode_encode_bhist :
    ∀ h : BHist, upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upgradeRegistryFields : UpgradeRegistryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpgradeRegistryUp.mk T S Nx F B A R H C P L => [T, S, Nx, F, B, A, R, H, C, P, L]

def upgradeRegistryToEventFlow : UpgradeRegistryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (upgradeRegistryFields x).map upgradeRegistryEncodeBHist

def upgradeRegistryFromEventFlow : EventFlow → Option UpgradeRegistryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | Nx :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | L :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (UpgradeRegistryUp.mk
                                                      (upgradeRegistryDecodeBHist T)
                                                      (upgradeRegistryDecodeBHist S)
                                                      (upgradeRegistryDecodeBHist Nx)
                                                      (upgradeRegistryDecodeBHist F)
                                                      (upgradeRegistryDecodeBHist B)
                                                      (upgradeRegistryDecodeBHist A)
                                                      (upgradeRegistryDecodeBHist R)
                                                      (upgradeRegistryDecodeBHist H)
                                                      (upgradeRegistryDecodeBHist C)
                                                      (upgradeRegistryDecodeBHist P)
                                                      (upgradeRegistryDecodeBHist L))
                                              | _ :: _ => none

private theorem upgradeRegistry_round_trip :
    ∀ x : UpgradeRegistryUp,
      upgradeRegistryFromEventFlow (upgradeRegistryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S Nx F B A R H C P L =>
      change
        some
          (UpgradeRegistryUp.mk
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist T))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist S))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist Nx))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist F))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist B))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist A))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist R))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist H))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist C))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist P))
            (upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist L))) =
          some (UpgradeRegistryUp.mk T S Nx F B A R H C P L)
      rw [upgradeRegistryDecode_encode_bhist T, upgradeRegistryDecode_encode_bhist S,
        upgradeRegistryDecode_encode_bhist Nx, upgradeRegistryDecode_encode_bhist F,
        upgradeRegistryDecode_encode_bhist B, upgradeRegistryDecode_encode_bhist A,
        upgradeRegistryDecode_encode_bhist R, upgradeRegistryDecode_encode_bhist H,
        upgradeRegistryDecode_encode_bhist C, upgradeRegistryDecode_encode_bhist P,
        upgradeRegistryDecode_encode_bhist L]

private theorem upgradeRegistryToEventFlow_injective {x y : UpgradeRegistryUp} :
    upgradeRegistryToEventFlow x = upgradeRegistryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upgradeRegistryFromEventFlow (upgradeRegistryToEventFlow x) =
        upgradeRegistryFromEventFlow (upgradeRegistryToEventFlow y) :=
    congrArg upgradeRegistryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (upgradeRegistry_round_trip x).symm
      (Eq.trans hread (upgradeRegistry_round_trip y)))

private theorem upgradeRegistry_fields_faithful :
    ∀ x y : UpgradeRegistryUp, upgradeRegistryFields x = upgradeRegistryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 S1 Nx1 F1 B1 A1 R1 H1 C1 P1 L1 =>
      cases y with
      | mk T2 S2 Nx2 F2 B2 A2 R2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance upgradeRegistryBHistCarrier : BHistCarrier UpgradeRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upgradeRegistryToEventFlow
  fromEventFlow := upgradeRegistryFromEventFlow

instance upgradeRegistryChapterTasteGate : ChapterTasteGate UpgradeRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upgradeRegistryFromEventFlow (upgradeRegistryToEventFlow x) = some x
    exact upgradeRegistry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upgradeRegistryToEventFlow_injective heq)

instance upgradeRegistryFieldFaithful : FieldFaithful UpgradeRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upgradeRegistryFields
  field_faithful := upgradeRegistry_fields_faithful

instance upgradeRegistryNontrivial : Nontrivial UpgradeRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpgradeRegistryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpgradeRegistryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UpgradeRegistryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  upgradeRegistryChapterTasteGate

namespace TasteGate

theorem UpgradeRegistryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UpgradeRegistryUp) ∧
      Nonempty (FieldFaithful UpgradeRegistryUp) ∧
        Nonempty (Nontrivial UpgradeRegistryUp) ∧
          (∀ h : BHist, upgradeRegistryDecodeBHist (upgradeRegistryEncodeBHist h) = h) ∧
            (∀ x : UpgradeRegistryUp,
              upgradeRegistryFromEventFlow (upgradeRegistryToEventFlow x) = some x) ∧
              (∀ x y : UpgradeRegistryUp,
                upgradeRegistryToEventFlow x = upgradeRegistryToEventFlow y → x = y) ∧
                upgradeRegistryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨upgradeRegistryChapterTasteGate⟩
  · constructor
    · exact ⟨upgradeRegistryFieldFaithful⟩
    · constructor
      · exact ⟨upgradeRegistryNontrivial⟩
      · constructor
        · exact upgradeRegistryDecode_encode_bhist
        · constructor
          · exact upgradeRegistry_round_trip
          · constructor
            · intro x y heq
              exact upgradeRegistryToEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate UpgradeRegistryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.UpgradeRegistryUp.taste_gate

end TasteGate

end BEDC.Derived.UpgradeRegistryUp
