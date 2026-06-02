import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OperatorNormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OperatorNormUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (T K L H C P N : BHist) : OperatorNormUp
  deriving DecidableEq

def operatorNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: operatorNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: operatorNormEncodeBHist h

def operatorNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (operatorNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (operatorNormDecodeBHist tail)

private theorem OperatorNormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, operatorNormDecodeBHist (operatorNormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem OperatorNormTasteGate_single_carrier_alignment_mk_congr
    {T1 T2 K1 K2 L1 L2 H1 H2 C1 C2 P1 P2 N1 N2 : BHist}
    (hT : T1 = T2) (hK : K1 = K2) (hL : L1 = L2) (hH : H1 = H2)
    (hC : C1 = C2) (hP : P1 = P2) (hN : N1 = N2) :
    OperatorNormUp.mk T1 K1 L1 H1 C1 P1 N1 =
      OperatorNormUp.mk T2 K2 L2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hK
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def operatorNormFields : OperatorNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OperatorNormUp.mk T K L H C P N => [T, K, L, H, C, P, N]

def operatorNormToEventFlow : OperatorNormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (operatorNormFields x).map operatorNormEncodeBHist

def operatorNormFromEventFlow : EventFlow → Option OperatorNormUp
  -- BEDC touchpoint anchor: BHist BMark
  | T :: restT =>
      match restT with
      | K :: restK =>
          match restK with
          | L :: restL =>
              match restL with
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
                                    (OperatorNormUp.mk
                                      (operatorNormDecodeBHist T)
                                      (operatorNormDecodeBHist K)
                                      (operatorNormDecodeBHist L)
                                      (operatorNormDecodeBHist H)
                                      (operatorNormDecodeBHist C)
                                      (operatorNormDecodeBHist P)
                                      (operatorNormDecodeBHist N))
                              | _ :: _ => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem OperatorNormTasteGate_single_carrier_alignment_round_trip
    (x : OperatorNormUp) :
    operatorNormFromEventFlow (operatorNormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T K L H C P N =>
      exact congrArg some
        (OperatorNormTasteGate_single_carrier_alignment_mk_congr
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode T)
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode K)
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode L)
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode H)
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode C)
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode P)
          (OperatorNormTasteGate_single_carrier_alignment_decode_encode N))

private theorem OperatorNormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OperatorNormUp} :
    operatorNormToEventFlow x = operatorNormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      operatorNormFromEventFlow (operatorNormToEventFlow x) =
        operatorNormFromEventFlow (operatorNormToEventFlow y) :=
    congrArg operatorNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OperatorNormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OperatorNormTasteGate_single_carrier_alignment_round_trip y)))

private theorem OperatorNormTasteGate_single_carrier_alignment_fields :
    ∀ x y : OperatorNormUp, operatorNormFields x = operatorNormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 K1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 K2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance operatorNormBHistCarrier : BHistCarrier OperatorNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := operatorNormToEventFlow
  fromEventFlow := operatorNormFromEventFlow

instance operatorNormChapterTasteGate : ChapterTasteGate OperatorNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change operatorNormFromEventFlow (operatorNormToEventFlow x) = some x
    exact OperatorNormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OperatorNormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance operatorNormFieldFaithful : FieldFaithful OperatorNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := operatorNormFields
  field_faithful := OperatorNormTasteGate_single_carrier_alignment_fields

instance operatorNormNontrivial :
    BEDC.Meta.TasteGate.Nontrivial OperatorNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OperatorNormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      OperatorNormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OperatorNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  operatorNormChapterTasteGate

theorem OperatorNormTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate OperatorNormUp) ∧
      Nonempty (FieldFaithful OperatorNormUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial OperatorNormUp) ∧
          (∀ h : BHist, operatorNormDecodeBHist (operatorNormEncodeBHist h) = h) ∧
            (∀ x : OperatorNormUp,
              operatorNormFromEventFlow (operatorNormToEventFlow x) = some x) ∧
              (∀ x y : OperatorNormUp,
                operatorNormToEventFlow x = operatorNormToEventFlow y → x = y) ∧
                operatorNormEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨{
        round_trip := by
          intro x
          change operatorNormFromEventFlow (operatorNormToEventFlow x) = some x
          exact OperatorNormTasteGate_single_carrier_alignment_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (OperatorNormTasteGate_single_carrier_alignment_toEventFlow_injective heq)
      }⟩,
      ⟨{
        fields := operatorNormFields
        field_faithful := OperatorNormTasteGate_single_carrier_alignment_fields
      }⟩,
      ⟨{
        witness_pair :=
          ⟨OperatorNormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty,
            OperatorNormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩
      }⟩,
      OperatorNormTasteGate_single_carrier_alignment_decode_encode,
      OperatorNormTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => OperatorNormTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.OperatorNormUp
