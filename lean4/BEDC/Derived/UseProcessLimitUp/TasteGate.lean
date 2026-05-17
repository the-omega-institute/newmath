import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UseProcessLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UseProcessLimitUp : Type where
  | mk :
      (N Uc R Pc L H C K Nc : BHist) →
      UseProcessLimitUp
  deriving DecidableEq

def useProcessLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: useProcessLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: useProcessLimitEncodeBHist h

def useProcessLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (useProcessLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (useProcessLimitDecodeBHist tail)

private theorem UseProcessLimitTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist, useProcessLimitDecodeBHist (useProcessLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem UseProcessLimitTasteGate_single_carrier_alignment_mk_aux
    {N N' Uc Uc' R R' Pc Pc' L L' H H' C C' K K' Nc Nc' : BHist}
    (hN : N' = N)
    (hUc : Uc' = Uc)
    (hR : R' = R)
    (hPc : Pc' = Pc)
    (hL : L' = L)
    (hH : H' = H)
    (hC : C' = C)
    (hK : K' = K)
    (hNc : Nc' = Nc) :
    UseProcessLimitUp.mk N' Uc' R' Pc' L' H' C' K' Nc' =
      UseProcessLimitUp.mk N Uc R Pc L H C K Nc := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hN
  cases hUc
  cases hR
  cases hPc
  cases hL
  cases hH
  cases hC
  cases hK
  cases hNc
  rfl

def useProcessLimitFields : UseProcessLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UseProcessLimitUp.mk N Uc R Pc L H C K Nc => [N, Uc, R, Pc, L, H, C, K, Nc]

def useProcessLimitToEventFlow : UseProcessLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UseProcessLimitUp.mk N Uc R Pc L H C K Nc =>
      [useProcessLimitEncodeBHist N,
        useProcessLimitEncodeBHist Uc,
        useProcessLimitEncodeBHist R,
        useProcessLimitEncodeBHist Pc,
        useProcessLimitEncodeBHist L,
        useProcessLimitEncodeBHist H,
        useProcessLimitEncodeBHist C,
        useProcessLimitEncodeBHist K,
        useProcessLimitEncodeBHist Nc]

def useProcessLimitFromEventFlow : EventFlow → Option UseProcessLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | N :: restN =>
      match restN with
      | [] => none
      | Uc :: restUc =>
          match restUc with
          | [] => none
          | R :: restR =>
              match restR with
              | [] => none
              | Pc :: restPc =>
                  match restPc with
                  | [] => none
                  | L :: restL =>
                      match restL with
                      | [] => none
                      | H :: restH =>
                          match restH with
                          | [] => none
                          | C :: restC =>
                              match restC with
                              | [] => none
                              | K :: restK =>
                                  match restK with
                                  | [] => none
                                  | Nc :: restNc =>
                                      match restNc with
                                      | [] =>
                                          some
                                            (UseProcessLimitUp.mk
                                              (useProcessLimitDecodeBHist N)
                                              (useProcessLimitDecodeBHist Uc)
                                              (useProcessLimitDecodeBHist R)
                                              (useProcessLimitDecodeBHist Pc)
                                              (useProcessLimitDecodeBHist L)
                                              (useProcessLimitDecodeBHist H)
                                              (useProcessLimitDecodeBHist C)
                                              (useProcessLimitDecodeBHist K)
                                              (useProcessLimitDecodeBHist Nc))
                                      | _ :: _ => none

private theorem UseProcessLimitTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : UseProcessLimitUp,
      useProcessLimitFromEventFlow (useProcessLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N Uc R Pc L H C K Nc =>
      exact
        congrArg some
          (UseProcessLimitTasteGate_single_carrier_alignment_mk_aux
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux N)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux Uc)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux R)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux Pc)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux L)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux H)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux C)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux K)
            (UseProcessLimitTasteGate_single_carrier_alignment_decode_aux Nc))

private theorem UseProcessLimitTasteGate_single_carrier_alignment_injective_aux
    {x y : UseProcessLimitUp} :
    useProcessLimitToEventFlow x = useProcessLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      useProcessLimitFromEventFlow (useProcessLimitToEventFlow x) =
        useProcessLimitFromEventFlow (useProcessLimitToEventFlow y) :=
    congrArg useProcessLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UseProcessLimitTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread
        (UseProcessLimitTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem UseProcessLimitTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : UseProcessLimitUp, useProcessLimitFields x = useProcessLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk N₁ Uc₁ R₁ Pc₁ L₁ H₁ C₁ K₁ Nc₁ =>
      cases y with
      | mk N₂ Uc₂ R₂ Pc₂ L₂ H₂ C₂ K₂ Nc₂ =>
          cases hfields
          rfl

instance useProcessLimitBHistCarrier :
    BHistCarrier UseProcessLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := useProcessLimitToEventFlow
  fromEventFlow := useProcessLimitFromEventFlow

instance useProcessLimitChapterTasteGate :
    ChapterTasteGate UseProcessLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change useProcessLimitFromEventFlow (useProcessLimitToEventFlow x) = some x
    exact UseProcessLimitTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UseProcessLimitTasteGate_single_carrier_alignment_injective_aux heq)

instance useProcessLimitFieldFaithful :
    FieldFaithful UseProcessLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := useProcessLimitFields
  field_faithful := by
    intro x y hfields
    exact UseProcessLimitTasteGate_single_carrier_alignment_fields_aux x y hfields

instance useProcessLimitNontrivial :
    Nontrivial UseProcessLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UseProcessLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UseProcessLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UseProcessLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, useProcessLimitDecodeBHist (useProcessLimitEncodeBHist h) = h) ∧
      (∀ x : UseProcessLimitUp,
        useProcessLimitFromEventFlow (useProcessLimitToEventFlow x) = some x) ∧
      (∀ x y : UseProcessLimitUp, useProcessLimitFields x = useProcessLimitFields y → x = y) ∧
      useProcessLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UseProcessLimitTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact UseProcessLimitTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · exact UseProcessLimitTasteGate_single_carrier_alignment_fields_aux
      · rfl

end BEDC.Derived.UseProcessLimitUp
