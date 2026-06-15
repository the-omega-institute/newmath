import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteJacobianUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteJacobianUp : Type where
  | mk (W M L E V H C P N : BHist) : FiniteJacobianUp
  deriving DecidableEq

def finiteJacobianEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteJacobianEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteJacobianEncodeBHist h

def finiteJacobianDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteJacobianDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteJacobianDecodeBHist tail)

private theorem FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist, finiteJacobianDecodeBHist (finiteJacobianEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteJacobianFields : FiniteJacobianUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteJacobianUp.mk W M L E V H C P N => [W, M, L, E, V, H, C, P, N]

def finiteJacobianToEventFlow : FiniteJacobianUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteJacobianFields x).map finiteJacobianEncodeBHist

def finiteJacobianFromEventFlow : EventFlow → Option FiniteJacobianUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: restW =>
      match restW with
      | M :: restM =>
          match restM with
          | L :: restL =>
              match restL with
              | E :: restE =>
                  match restE with
                  | V :: restV =>
                      match restV with
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
                                            (FiniteJacobianUp.mk
                                              (finiteJacobianDecodeBHist W)
                                              (finiteJacobianDecodeBHist M)
                                              (finiteJacobianDecodeBHist L)
                                              (finiteJacobianDecodeBHist E)
                                              (finiteJacobianDecodeBHist V)
                                              (finiteJacobianDecodeBHist H)
                                              (finiteJacobianDecodeBHist C)
                                              (finiteJacobianDecodeBHist P)
                                              (finiteJacobianDecodeBHist N))
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

private theorem FiniteJacobianTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteJacobianUp,
      finiteJacobianFromEventFlow (finiteJacobianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W M L E V H C P N =>
      change
        some
          (FiniteJacobianUp.mk
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist W))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist M))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist L))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist E))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist V))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist H))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist C))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist P))
            (finiteJacobianDecodeBHist (finiteJacobianEncodeBHist N))) =
          some (FiniteJacobianUp.mk W M L E V H C P N)
      rw [FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist W,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist M,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist L,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist E,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist V,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist H,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist C,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist P,
        FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist N]

private theorem finiteJacobianToEventFlow_injective {x y : FiniteJacobianUp} :
    finiteJacobianToEventFlow x = finiteJacobianToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteJacobianFromEventFlow (finiteJacobianToEventFlow x) =
        finiteJacobianFromEventFlow (finiteJacobianToEventFlow y) :=
    congrArg finiteJacobianFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteJacobianTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteJacobianTasteGate_single_carrier_alignment_round_trip y)))

theorem FiniteJacobianTasteGate_single_carrier_alignment_field_faithful :
    forall x y : FiniteJacobianUp, finiteJacobianFields x = finiteJacobianFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W M L E V H C P N =>
      cases y with
      | mk W' M' L' E' V' H' C' P' N' =>
          cases hfields
          rfl

instance finiteJacobianBHistCarrier : BHistCarrier FiniteJacobianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteJacobianToEventFlow
  fromEventFlow := finiteJacobianFromEventFlow

instance finiteJacobianChapterTasteGate : ChapterTasteGate FiniteJacobianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (FiniteJacobianTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteJacobianToEventFlow_injective heq)

instance finiteJacobianFieldFaithful : FieldFaithful FiniteJacobianUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteJacobianFields
  field_faithful := FiniteJacobianTasteGate_single_carrier_alignment_field_faithful

instance finiteJacobianNontrivial : BEDC.Meta.TasteGate.Nontrivial FiniteJacobianUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteJacobianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteJacobianUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteJacobianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteJacobianChapterTasteGate

theorem FiniteJacobianTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteJacobianUp) ∧
      Nonempty (FieldFaithful FiniteJacobianUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteJacobianUp) ∧
      (∀ h : BHist, finiteJacobianDecodeBHist (finiteJacobianEncodeBHist h) = h) ∧
      finiteJacobianDecodeBHist [BMark.b1] = BHist.e1 BHist.Empty ∧
      ∀ x : FiniteJacobianUp,
        finiteJacobianFromEventFlow (finiteJacobianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨finiteJacobianChapterTasteGate⟩
  constructor
  · exact ⟨finiteJacobianFieldFaithful⟩
  constructor
  · exact ⟨finiteJacobianNontrivial⟩
  constructor
  · exact FiniteJacobianTasteGate_single_carrier_alignment_decode_encode_bhist
  constructor
  · rfl
  · exact FiniteJacobianTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.FiniteJacobianUp
