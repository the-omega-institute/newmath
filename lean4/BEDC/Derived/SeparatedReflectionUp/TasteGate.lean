import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedReflectionUp : Type where
  | mk (P0 Z S M R E H C N : BHist) : SeparatedReflectionUp
  deriving DecidableEq

def separatedReflectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 t => BMark.b0 :: separatedReflectionEncodeBHist t
  | BHist.e1 t => BMark.b1 :: separatedReflectionEncodeBHist t

def separatedReflectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedReflectionDecodeBHist tail)

private theorem SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, separatedReflectionDecodeBHist (separatedReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def separatedReflectionFields : SeparatedReflectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedReflectionUp.mk P0 Z S M R E H C N => [P0, Z, S, M, R, E, H, C, N]

def separatedReflectionToEventFlow : SeparatedReflectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separatedReflectionFields x).map separatedReflectionEncodeBHist

def separatedReflectionFromEventFlow : EventFlow -> Option SeparatedReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | P0 :: Z :: S :: M :: R :: E :: H :: C :: N :: [] =>
      some
        (SeparatedReflectionUp.mk
          (separatedReflectionDecodeBHist P0)
          (separatedReflectionDecodeBHist Z)
          (separatedReflectionDecodeBHist S)
          (separatedReflectionDecodeBHist M)
          (separatedReflectionDecodeBHist R)
          (separatedReflectionDecodeBHist E)
          (separatedReflectionDecodeBHist H)
          (separatedReflectionDecodeBHist C)
          (separatedReflectionDecodeBHist N))
  | _ => none

private theorem SeparatedReflectionTasteGate_single_carrier_alignment_round_trip :
    forall x : SeparatedReflectionUp,
      separatedReflectionFromEventFlow (separatedReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P0 Z S M R E H C N =>
      change
        some
          (SeparatedReflectionUp.mk
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist P0))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist Z))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist S))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist M))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist R))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist E))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist H))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist C))
            (separatedReflectionDecodeBHist (separatedReflectionEncodeBHist N))) =
          some (SeparatedReflectionUp.mk P0 Z S M R E H C N)
      rw [SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode P0,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode Z,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode S,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode M,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode R,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode E,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode H,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode C,
        SeparatedReflectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem SeparatedReflectionTasteGate_single_carrier_alignment_injective
    {x y : SeparatedReflectionUp} :
    separatedReflectionToEventFlow x = separatedReflectionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedReflectionFromEventFlow (separatedReflectionToEventFlow x) =
        separatedReflectionFromEventFlow (separatedReflectionToEventFlow y) :=
    congrArg separatedReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SeparatedReflectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeparatedReflectionTasteGate_single_carrier_alignment_field_faithful :
    forall x y : SeparatedReflectionUp, separatedReflectionFields x = separatedReflectionFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk P01 Z1 S1 M1 R1 E1 H1 C1 N1 =>
      cases y with
      | mk P02 Z2 S2 M2 R2 E2 H2 C2 N2 =>
          injection h with hP0 t1
          injection t1 with hZ t2
          injection t2 with hS t3
          injection t3 with hM t4
          injection t4 with hR t5
          injection t5 with hE t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hN _
          subst hP0
          subst hZ
          subst hS
          subst hM
          subst hR
          subst hE
          subst hH
          subst hC
          subst hN
          rfl

instance separatedReflectionBHistCarrier : BHistCarrier SeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedReflectionToEventFlow
  fromEventFlow := separatedReflectionFromEventFlow

instance separatedReflectionChapterTasteGate : ChapterTasteGate SeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedReflectionFromEventFlow (separatedReflectionToEventFlow x) = some x
    exact SeparatedReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeparatedReflectionTasteGate_single_carrier_alignment_injective heq)

instance separatedReflectionFieldFaithful : FieldFaithful SeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedReflectionFields
  field_faithful := SeparatedReflectionTasteGate_single_carrier_alignment_field_faithful

instance separatedReflectionNontrivial : Nontrivial SeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparatedReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedReflectionChapterTasteGate

theorem SeparatedReflectionTasteGate_single_carrier_alignment :
    (forall h : BHist, separatedReflectionDecodeBHist (separatedReflectionEncodeBHist h) = h) ∧
      (forall P0 Z S M R E H C N : BHist,
        separatedReflectionFields (SeparatedReflectionUp.mk P0 Z S M R E H C N) =
          [P0, Z, S, M, R, E, H, C, N]) ∧
        separatedReflectionToEventFlow
            (SeparatedReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[], [], [], [], [], [], [], [], []] ∧
          separatedReflectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro P0 Z S M R E H C N
      rfl
    · constructor
      · rfl
      · rfl

end BEDC.Derived.SeparatedReflectionUp
