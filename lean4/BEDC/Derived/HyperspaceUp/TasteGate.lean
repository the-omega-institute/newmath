import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperspaceUp : Type where
  | mk (X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist) : HyperspaceUp
  deriving DecidableEq

def hyperspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperspaceEncodeBHist h

def hyperspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperspaceDecodeBHist tail)

private theorem hyperspaceDecode_encode_bhist :
    ∀ h : BHist, hyperspaceDecodeBHist (hyperspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperspaceFields : HyperspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperspaceUp.mk X K0 K1 N0 N1 D0 D1 R Hs C P M =>
      [X, K0, K1, N0, N1, D0, D1, R, Hs, C, P, M]

def hyperspaceToEventFlow : HyperspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperspaceFields x).map hyperspaceEncodeBHist

def hyperspaceFromEventFlow : EventFlow → Option HyperspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | K0 :: rest1 =>
          match rest1 with
          | [] => none
          | K1 :: rest2 =>
              match rest2 with
              | [] => none
              | N0 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | N1 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D1 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Hs :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | M :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (HyperspaceUp.mk
                                                          (hyperspaceDecodeBHist X)
                                                          (hyperspaceDecodeBHist K0)
                                                          (hyperspaceDecodeBHist K1)
                                                          (hyperspaceDecodeBHist N0)
                                                          (hyperspaceDecodeBHist N1)
                                                          (hyperspaceDecodeBHist D0)
                                                          (hyperspaceDecodeBHist D1)
                                                          (hyperspaceDecodeBHist R)
                                                          (hyperspaceDecodeBHist Hs)
                                                          (hyperspaceDecodeBHist C)
                                                          (hyperspaceDecodeBHist P)
                                                          (hyperspaceDecodeBHist M))
                                                  | _ :: _ => none

private theorem hyperspace_round_trip :
    ∀ x : HyperspaceUp, hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K0 K1 N0 N1 D0 D1 R Hs C P M =>
      change
        some
          (HyperspaceUp.mk
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist X))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist K0))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist K1))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist N0))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist N1))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist D0))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist D1))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist R))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist Hs))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist C))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist P))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist M))) =
          some (HyperspaceUp.mk X K0 K1 N0 N1 D0 D1 R Hs C P M)
      rw [hyperspaceDecode_encode_bhist X, hyperspaceDecode_encode_bhist K0,
        hyperspaceDecode_encode_bhist K1, hyperspaceDecode_encode_bhist N0,
        hyperspaceDecode_encode_bhist N1, hyperspaceDecode_encode_bhist D0,
        hyperspaceDecode_encode_bhist D1, hyperspaceDecode_encode_bhist R,
        hyperspaceDecode_encode_bhist Hs, hyperspaceDecode_encode_bhist C,
        hyperspaceDecode_encode_bhist P, hyperspaceDecode_encode_bhist M]

private theorem hyperspaceToEventFlow_injective {x y : HyperspaceUp} :
    hyperspaceToEventFlow x = hyperspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperspaceFromEventFlow (hyperspaceToEventFlow x) =
        hyperspaceFromEventFlow (hyperspaceToEventFlow y) :=
    congrArg hyperspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperspace_round_trip x).symm (Eq.trans hread (hyperspace_round_trip y)))

private theorem hyperspace_fields_faithful :
    ∀ x y : HyperspaceUp, hyperspaceFields x = hyperspaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 K01 K11 N01 N11 D01 D11 R1 Hs1 C1 P1 M1 =>
      cases y with
      | mk X2 K02 K12 N02 N12 D02 D12 R2 Hs2 C2 P2 M2 =>
          cases hfields
          rfl

instance hyperspaceBHistCarrier : BHistCarrier HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperspaceToEventFlow
  fromEventFlow := hyperspaceFromEventFlow

instance hyperspaceChapterTasteGate : ChapterTasteGate HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x
    exact hyperspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperspaceToEventFlow_injective heq)

instance hyperspaceFieldFaithful : FieldFaithful HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperspaceFields
  field_faithful := hyperspace_fields_faithful

instance hyperspaceNontrivial : Nontrivial HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperspaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperspaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HyperspaceUp) ∧ Nonempty (FieldFaithful HyperspaceUp) ∧
      Nonempty (Nontrivial HyperspaceUp) ∧
        (∀ h : BHist, hyperspaceDecodeBHist (hyperspaceEncodeBHist h) = h) ∧
          (∀ x : HyperspaceUp,
            hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x) ∧
            hyperspaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨hyperspaceChapterTasteGate⟩
  · constructor
    · exact ⟨hyperspaceFieldFaithful⟩
    · constructor
      · exact ⟨hyperspaceNontrivial⟩
      · constructor
        · exact hyperspaceDecode_encode_bhist
        · constructor
          · exact hyperspace_round_trip
          · rfl

end BEDC.Derived.HyperspaceUp
