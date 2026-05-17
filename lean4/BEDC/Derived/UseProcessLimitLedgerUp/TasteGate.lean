import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UseProcessLimitLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UseProcessLimitLedgerUp : Type where
  | mk :
      (U C Lf H R P N : BHist) →
      UseProcessLimitLedgerUp
  deriving DecidableEq

def useProcessLimitLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: useProcessLimitLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: useProcessLimitLedgerEncodeBHist h

def useProcessLimitLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (useProcessLimitLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (useProcessLimitLedgerDecodeBHist tail)

private theorem UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      useProcessLimitLedgerDecodeBHist (useProcessLimitLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem UseProcessLimitLedgerTasteGate_single_carrier_alignment_mk_aux
    {U U' C C' Lf Lf' H H' R R' P P' N N' : BHist}
    (hU : U' = U)
    (hC : C' = C)
    (hLf : Lf' = Lf)
    (hH : H' = H)
    (hR : R' = R)
    (hP : P' = P)
    (hN : N' = N) :
    UseProcessLimitLedgerUp.mk U' C' Lf' H' R' P' N' =
      UseProcessLimitLedgerUp.mk U C Lf H R P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hU
  cases hC
  cases hLf
  cases hH
  cases hR
  cases hP
  cases hN
  rfl

def useProcessLimitLedgerFields : UseProcessLimitLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UseProcessLimitLedgerUp.mk U C Lf H R P N => [U, C, Lf, H, R, P, N]

def useProcessLimitLedgerToEventFlow : UseProcessLimitLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UseProcessLimitLedgerUp.mk U C Lf H R P N =>
      [useProcessLimitLedgerEncodeBHist U,
        useProcessLimitLedgerEncodeBHist C,
        useProcessLimitLedgerEncodeBHist Lf,
        useProcessLimitLedgerEncodeBHist H,
        useProcessLimitLedgerEncodeBHist R,
        useProcessLimitLedgerEncodeBHist P,
        useProcessLimitLedgerEncodeBHist N]

def useProcessLimitLedgerFromEventFlow :
    EventFlow → Option UseProcessLimitLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: restU =>
      match restU with
      | [] => none
      | C :: restC =>
          match restC with
          | [] => none
          | Lf :: restLf =>
              match restLf with
              | [] => none
              | H :: restH =>
                  match restH with
                  | [] => none
                  | R :: restR =>
                      match restR with
                      | [] => none
                      | P :: restP =>
                          match restP with
                          | [] => none
                          | N :: restN =>
                              match restN with
                              | [] =>
                                  some
                                    (UseProcessLimitLedgerUp.mk
                                      (useProcessLimitLedgerDecodeBHist U)
                                      (useProcessLimitLedgerDecodeBHist C)
                                      (useProcessLimitLedgerDecodeBHist Lf)
                                      (useProcessLimitLedgerDecodeBHist H)
                                      (useProcessLimitLedgerDecodeBHist R)
                                      (useProcessLimitLedgerDecodeBHist P)
                                      (useProcessLimitLedgerDecodeBHist N))
                              | _ :: _ => none

private theorem UseProcessLimitLedgerTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : UseProcessLimitLedgerUp,
      useProcessLimitLedgerFromEventFlow (useProcessLimitLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U C Lf H R P N =>
      exact
        congrArg some
          (UseProcessLimitLedgerTasteGate_single_carrier_alignment_mk_aux
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux U)
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux C)
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux Lf)
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux H)
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux R)
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux P)
            (UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux N))

private theorem UseProcessLimitLedgerTasteGate_single_carrier_alignment_injective_aux
    {x y : UseProcessLimitLedgerUp} :
    useProcessLimitLedgerToEventFlow x = useProcessLimitLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      useProcessLimitLedgerFromEventFlow (useProcessLimitLedgerToEventFlow x) =
        useProcessLimitLedgerFromEventFlow (useProcessLimitLedgerToEventFlow y) :=
    congrArg useProcessLimitLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UseProcessLimitLedgerTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread
        (UseProcessLimitLedgerTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem UseProcessLimitLedgerTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : UseProcessLimitLedgerUp,
      useProcessLimitLedgerFields x = useProcessLimitLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ C₁ Lf₁ H₁ R₁ P₁ N₁ =>
      cases y with
      | mk U₂ C₂ Lf₂ H₂ R₂ P₂ N₂ =>
          cases hfields
          rfl

instance useProcessLimitLedgerBHistCarrier :
    BHistCarrier UseProcessLimitLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := useProcessLimitLedgerToEventFlow
  fromEventFlow := useProcessLimitLedgerFromEventFlow

instance useProcessLimitLedgerChapterTasteGate :
    ChapterTasteGate UseProcessLimitLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change useProcessLimitLedgerFromEventFlow (useProcessLimitLedgerToEventFlow x) = some x
    exact UseProcessLimitLedgerTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UseProcessLimitLedgerTasteGate_single_carrier_alignment_injective_aux heq)

instance useProcessLimitLedgerFieldFaithful :
    FieldFaithful UseProcessLimitLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := useProcessLimitLedgerFields
  field_faithful := by
    intro x y hfields
    exact UseProcessLimitLedgerTasteGate_single_carrier_alignment_fields_aux x y hfields

instance useProcessLimitLedgerNontrivial :
    Nontrivial UseProcessLimitLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UseProcessLimitLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      UseProcessLimitLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UseProcessLimitLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        useProcessLimitLedgerDecodeBHist (useProcessLimitLedgerEncodeBHist h) = h) ∧
      (∀ x : UseProcessLimitLedgerUp,
        useProcessLimitLedgerFromEventFlow (useProcessLimitLedgerToEventFlow x) =
          some x) ∧
      (∀ x y : UseProcessLimitLedgerUp,
        useProcessLimitLedgerFields x = useProcessLimitLedgerFields y → x = y) ∧
      (∃ x y : UseProcessLimitLedgerUp, x ≠ y) ∧
      useProcessLimitLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UseProcessLimitLedgerTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact UseProcessLimitLedgerTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · exact UseProcessLimitLedgerTasteGate_single_carrier_alignment_fields_aux
      · constructor
        · exact
            ⟨UseProcessLimitLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              UseProcessLimitLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end BEDC.Derived.UseProcessLimitLedgerUp
