import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannLebesgueLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannLebesgueLemmaUp : Type where
  | mk (F S I W T A Q E H C P N : BHist) : RiemannLebesgueLemmaUp
  deriving DecidableEq

def riemannLebesgueLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannLebesgueLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannLebesgueLemmaEncodeBHist h

def riemannLebesgueLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannLebesgueLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannLebesgueLemmaDecodeBHist tail)

private theorem riemannLebesgueLemma_decode_encode :
    ∀ h : BHist, riemannLebesgueLemmaDecodeBHist
      (riemannLebesgueLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannLebesgueLemmaFields : RiemannLebesgueLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannLebesgueLemmaUp.mk F S I W T A Q E H C P N =>
      [F, S, I, W, T, A, Q, E, H, C, P, N]

def riemannLebesgueLemmaToEventFlow : RiemannLebesgueLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (riemannLebesgueLemmaFields token).map riemannLebesgueLemmaEncodeBHist

def riemannLebesgueLemmaFromEventFlow : EventFlow → Option RiemannLebesgueLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | S :: restS =>
          match restS with
          | I :: restI =>
              match restI with
              | W :: restW =>
                  match restW with
                  | T :: restT =>
                      match restT with
                      | A :: restA =>
                          match restA with
                          | Q :: restQ =>
                              match restQ with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (RiemannLebesgueLemmaUp.mk
                                                          (riemannLebesgueLemmaDecodeBHist F)
                                                          (riemannLebesgueLemmaDecodeBHist S)
                                                          (riemannLebesgueLemmaDecodeBHist I)
                                                          (riemannLebesgueLemmaDecodeBHist W)
                                                          (riemannLebesgueLemmaDecodeBHist T)
                                                          (riemannLebesgueLemmaDecodeBHist A)
                                                          (riemannLebesgueLemmaDecodeBHist Q)
                                                          (riemannLebesgueLemmaDecodeBHist E)
                                                          (riemannLebesgueLemmaDecodeBHist H)
                                                          (riemannLebesgueLemmaDecodeBHist C)
                                                          (riemannLebesgueLemmaDecodeBHist P)
                                                          (riemannLebesgueLemmaDecodeBHist N))
                                                  | _ :: _ => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem riemannLebesgueLemma_round_trip :
    ∀ token : RiemannLebesgueLemmaUp,
      riemannLebesgueLemmaFromEventFlow (riemannLebesgueLemmaToEventFlow token) =
        some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F S I W T A Q E H C P N =>
      change
        some
            (RiemannLebesgueLemmaUp.mk
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist F))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist S))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist I))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist W))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist T))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist A))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist Q))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist E))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist H))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist C))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist P))
              (riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist N))) =
          some (RiemannLebesgueLemmaUp.mk F S I W T A Q E H C P N)
      rw [riemannLebesgueLemma_decode_encode F]
      rw [riemannLebesgueLemma_decode_encode S]
      rw [riemannLebesgueLemma_decode_encode I]
      rw [riemannLebesgueLemma_decode_encode W]
      rw [riemannLebesgueLemma_decode_encode T]
      rw [riemannLebesgueLemma_decode_encode A]
      rw [riemannLebesgueLemma_decode_encode Q]
      rw [riemannLebesgueLemma_decode_encode E]
      rw [riemannLebesgueLemma_decode_encode H]
      rw [riemannLebesgueLemma_decode_encode C]
      rw [riemannLebesgueLemma_decode_encode P]
      rw [riemannLebesgueLemma_decode_encode N]

private theorem riemannLebesgueLemmaToEventFlow_injective
    {x y : RiemannLebesgueLemmaUp} :
    riemannLebesgueLemmaToEventFlow x = riemannLebesgueLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannLebesgueLemmaFromEventFlow (riemannLebesgueLemmaToEventFlow x) =
        riemannLebesgueLemmaFromEventFlow (riemannLebesgueLemmaToEventFlow y) :=
    congrArg riemannLebesgueLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (riemannLebesgueLemma_round_trip x).symm
      (Eq.trans hread (riemannLebesgueLemma_round_trip y)))

private theorem RiemannLebesgueLemmaTasteGate_single_carrier_alignment_fields :
    ∀ x y : RiemannLebesgueLemmaUp,
      riemannLebesgueLemmaFields x = riemannLebesgueLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 S1 I1 W1 T1 A1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 S2 I2 W2 T2 A2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance riemannLebesgueLemmaBHistCarrier : BHistCarrier RiemannLebesgueLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannLebesgueLemmaToEventFlow
  fromEventFlow := riemannLebesgueLemmaFromEventFlow

instance riemannLebesgueLemmaChapterTasteGate :
    ChapterTasteGate RiemannLebesgueLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannLebesgueLemmaFromEventFlow (riemannLebesgueLemmaToEventFlow x) = some x
    exact riemannLebesgueLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (riemannLebesgueLemmaToEventFlow_injective heq)

instance riemannLebesgueLemmaFieldFaithful : FieldFaithful RiemannLebesgueLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannLebesgueLemmaFields
  field_faithful := RiemannLebesgueLemmaTasteGate_single_carrier_alignment_fields

instance riemannLebesgueLemmaNontrivial : Nontrivial RiemannLebesgueLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannLebesgueLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RiemannLebesgueLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RiemannLebesgueLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        riemannLebesgueLemmaDecodeBHist (riemannLebesgueLemmaEncodeBHist h) = h) ∧
      (∀ x : RiemannLebesgueLemmaUp,
        riemannLebesgueLemmaFromEventFlow (riemannLebesgueLemmaToEventFlow x) = some x) ∧
      (∀ x y : RiemannLebesgueLemmaUp,
        riemannLebesgueLemmaToEventFlow x = riemannLebesgueLemmaToEventFlow y → x = y) ∧
      riemannLebesgueLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact riemannLebesgueLemma_decode_encode
  · constructor
    · exact riemannLebesgueLemma_round_trip
    · constructor
      · intro x y
        exact riemannLebesgueLemmaToEventFlow_injective
      · rfl

end BEDC.Derived.RiemannLebesgueLemmaUp
