import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySeriesProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySeriesProductUp : Type where
  | mk (S T C B M R E H P N : BHist) : CauchySeriesProductUp
  deriving DecidableEq

def cauchySeriesProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySeriesProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySeriesProductEncodeBHist h

def cauchySeriesProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySeriesProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySeriesProductDecodeBHist tail)

private theorem cauchySeriesProductDecode_encode :
    ∀ h : BHist,
      cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySeriesProductFields : CauchySeriesProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySeriesProductUp.mk S T C B M R E H P N => [S, T, C, B, M, R, E, H, P, N]

def cauchySeriesProductToEventFlow : CauchySeriesProductUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySeriesProductFields x).map cauchySeriesProductEncodeBHist

def cauchySeriesProductFromEventFlow : EventFlow → Option CauchySeriesProductUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restT =>
      match restT with
      | [] => none
      | T :: restC =>
          match restC with
          | [] => none
          | C :: restB =>
              match restB with
              | [] => none
              | B :: restM =>
                  match restM with
                  | [] => none
                  | M :: restR =>
                      match restR with
                      | [] => none
                      | R :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
                              match restH with
                              | [] => none
                              | H :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchySeriesProductUp.mk
                                                  (cauchySeriesProductDecodeBHist S)
                                                  (cauchySeriesProductDecodeBHist T)
                                                  (cauchySeriesProductDecodeBHist C)
                                                  (cauchySeriesProductDecodeBHist B)
                                                  (cauchySeriesProductDecodeBHist M)
                                                  (cauchySeriesProductDecodeBHist R)
                                                  (cauchySeriesProductDecodeBHist E)
                                                  (cauchySeriesProductDecodeBHist H)
                                                  (cauchySeriesProductDecodeBHist P)
                                                  (cauchySeriesProductDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchySeriesProduct_round_trip :
    ∀ x : CauchySeriesProductUp,
      cauchySeriesProductFromEventFlow
        (cauchySeriesProductToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T C B M R E H P N =>
      change
        some
          (CauchySeriesProductUp.mk
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist S))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist T))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist C))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist B))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist M))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist R))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist E))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist H))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist P))
            (cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist N))) =
          some (CauchySeriesProductUp.mk S T C B M R E H P N)
      rw [cauchySeriesProductDecode_encode S, cauchySeriesProductDecode_encode T,
        cauchySeriesProductDecode_encode C, cauchySeriesProductDecode_encode B,
        cauchySeriesProductDecode_encode M, cauchySeriesProductDecode_encode R,
        cauchySeriesProductDecode_encode E, cauchySeriesProductDecode_encode H,
        cauchySeriesProductDecode_encode P, cauchySeriesProductDecode_encode N]

private theorem cauchySeriesProductToEventFlow_injective
    {x y : CauchySeriesProductUp} :
    cauchySeriesProductToEventFlow x = cauchySeriesProductToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySeriesProductFromEventFlow (cauchySeriesProductToEventFlow x) =
        cauchySeriesProductFromEventFlow (cauchySeriesProductToEventFlow y) :=
    congrArg cauchySeriesProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySeriesProduct_round_trip x).symm
      (Eq.trans hread (cauchySeriesProduct_round_trip y)))

private theorem cauchySeriesProductFields_faithful :
    ∀ x y : CauchySeriesProductUp,
      cauchySeriesProductFields x = cauchySeriesProductFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 T1 C1 B1 M1 R1 E1 H1 P1 N1 =>
      cases y with
      | mk S2 T2 C2 B2 M2 R2 E2 H2 P2 N2 =>
          cases h
          rfl

instance cauchySeriesProductBHistCarrier : BHistCarrier CauchySeriesProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySeriesProductToEventFlow
  fromEventFlow := cauchySeriesProductFromEventFlow

instance cauchySeriesProductChapterTasteGate :
    ChapterTasteGate CauchySeriesProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySeriesProductFromEventFlow
        (cauchySeriesProductToEventFlow x) = some x
    exact cauchySeriesProduct_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySeriesProductToEventFlow_injective heq)

instance cauchySeriesProductFieldFaithful :
    FieldFaithful CauchySeriesProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySeriesProductFields
  field_faithful := cauchySeriesProductFields_faithful

instance cauchySeriesProductNontrivial :
    Nontrivial CauchySeriesProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySeriesProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySeriesProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySeriesProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

namespace TasteGate

theorem CauchySeriesProductTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchySeriesProductUp) ∧
      Nonempty (FieldFaithful CauchySeriesProductUp) ∧
        Nonempty (Nontrivial CauchySeriesProductUp) ∧
          (∀ h : BHist,
            cauchySeriesProductDecodeBHist (cauchySeriesProductEncodeBHist h) = h) ∧
            (∀ x : CauchySeriesProductUp,
              cauchySeriesProductFromEventFlow
                (cauchySeriesProductToEventFlow x) = some x) ∧
              (∀ x y : CauchySeriesProductUp,
                cauchySeriesProductToEventFlow x =
                  cauchySeriesProductToEventFlow y → x = y) ∧
                cauchySeriesProductEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨inferInstance⟩
  · constructor
    · exact ⟨inferInstance⟩
    · constructor
      · exact ⟨inferInstance⟩
      · constructor
        · exact cauchySeriesProductDecode_encode
        · constructor
          · exact cauchySeriesProduct_round_trip
          · constructor
            · intro x y heq
              exact cauchySeriesProductToEventFlow_injective heq
            · rfl

end TasteGate

end BEDC.Derived.CauchySeriesProductUp
