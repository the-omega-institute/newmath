import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophyGapMapLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophyGapMapLedgerUp : Type where
  | mk : (E S K T U F A H C P N : BHist) → PhilosophyGapMapLedgerUp
  deriving DecidableEq

def philosophyGapMapLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophyGapMapLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophyGapMapLedgerEncodeBHist h

def philosophyGapMapLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophyGapMapLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophyGapMapLedgerDecodeBHist tail)

theorem PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem philosophyGapMapLedger_mk_congr
    {E E' S S' K K' T T' U U' F F' A A' H H' C C' P P' N N' : BHist}
    (hE : E' = E) (hS : S' = S) (hK : K' = K) (hT : T' = T) (hU : U' = U)
    (hF : F' = F) (hA : A' = A) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    PhilosophyGapMapLedgerUp.mk E' S' K' T' U' F' A' H' C' P' N' =
      PhilosophyGapMapLedgerUp.mk E S K T U F A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hE
  cases hS
  cases hK
  cases hT
  cases hU
  cases hF
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def philosophyGapMapLedgerToEventFlow : PhilosophyGapMapLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyGapMapLedgerUp.mk E S K T U F A H C P N =>
      [[BMark.b0, BMark.b0, BMark.b1],
        philosophyGapMapLedgerEncodeBHist E,
        philosophyGapMapLedgerEncodeBHist S,
        philosophyGapMapLedgerEncodeBHist K,
        philosophyGapMapLedgerEncodeBHist T,
        philosophyGapMapLedgerEncodeBHist U,
        philosophyGapMapLedgerEncodeBHist F,
        philosophyGapMapLedgerEncodeBHist A,
        philosophyGapMapLedgerEncodeBHist H,
        philosophyGapMapLedgerEncodeBHist C,
        philosophyGapMapLedgerEncodeBHist P,
        philosophyGapMapLedgerEncodeBHist N]

private def philosophyGapMapLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => philosophyGapMapLedgerEventAtDefault index rest

def philosophyGapMapLedgerFromEventFlow :
    EventFlow → Option PhilosophyGapMapLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PhilosophyGapMapLedgerUp.mk
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 1 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 2 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 3 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 4 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 5 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 6 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 7 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 8 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 9 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 10 ef))
        (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEventAtDefault 11 ef)))

def philosophyGapMapLedgerFields : PhilosophyGapMapLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyGapMapLedgerUp.mk E S K T U F A H C P N => [E, S, K, T, U, F, A, H, C, P, N]

theorem PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PhilosophyGapMapLedgerUp,
      philosophyGapMapLedgerFromEventFlow (philosophyGapMapLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E S K T U F A H C P N =>
      change
        some
          (PhilosophyGapMapLedgerUp.mk
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist E))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist S))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist K))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist T))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist U))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist F))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist A))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist H))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist C))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist P))
            (philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist N))) =
          some (PhilosophyGapMapLedgerUp.mk E S K T U F A H C P N)
      rw [PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode E,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode S,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode K,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode T,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode U,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode F,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode A,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode H,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode C,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode P,
        PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode N]

theorem PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_injective
    {x y : PhilosophyGapMapLedgerUp} :
    philosophyGapMapLedgerToEventFlow x = philosophyGapMapLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophyGapMapLedgerFromEventFlow (philosophyGapMapLedgerToEventFlow x) =
        philosophyGapMapLedgerFromEventFlow (philosophyGapMapLedgerToEventFlow y) :=
    congrArg philosophyGapMapLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem philosophyGapMapLedger_field_faithful :
    ∀ x y : PhilosophyGapMapLedgerUp,
      philosophyGapMapLedgerFields x = philosophyGapMapLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk E₁ S₁ K₁ T₁ U₁ F₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ S₂ K₂ T₂ U₂ F₂ A₂ H₂ C₂ P₂ N₂ =>
          injection h with hE t1
          injection t1 with hS t2
          injection t2 with hK t3
          injection t3 with hT t4
          injection t4 with hU t5
          injection t5 with hF t6
          injection t6 with hA t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          cases hE
          cases hS
          cases hK
          cases hT
          cases hU
          cases hF
          cases hA
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance philosophyGapMapLedgerBHistCarrier : BHistCarrier PhilosophyGapMapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophyGapMapLedgerToEventFlow
  fromEventFlow := philosophyGapMapLedgerFromEventFlow

instance philosophyGapMapLedgerChapterTasteGate :
    ChapterTasteGate PhilosophyGapMapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change philosophyGapMapLedgerFromEventFlow (philosophyGapMapLedgerToEventFlow x) = some x
    exact PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_injective heq)

instance philosophyGapMapLedgerFieldFaithful : FieldFaithful PhilosophyGapMapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophyGapMapLedgerFields
  field_faithful := philosophyGapMapLedger_field_faithful

instance philosophyGapMapLedgerNontrivial : Nontrivial PhilosophyGapMapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophyGapMapLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophyGapMapLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhilosophyGapMapLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyGapMapLedgerChapterTasteGate

def taste_gate_witness : FieldFaithful PhilosophyGapMapLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyGapMapLedgerFieldFaithful

theorem PhilosophyGapMapLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, philosophyGapMapLedgerDecodeBHist (philosophyGapMapLedgerEncodeBHist h) = h) ∧
      (∀ x : PhilosophyGapMapLedgerUp,
        philosophyGapMapLedgerFromEventFlow (philosophyGapMapLedgerToEventFlow x) = some x) ∧
        (∀ x y : PhilosophyGapMapLedgerUp,
          philosophyGapMapLedgerToEventFlow x = philosophyGapMapLedgerToEventFlow y → x = y) ∧
          philosophyGapMapLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_decode
  · constructor
    · exact PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PhilosophyGapMapLedgerTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.PhilosophyGapMapLedgerUp
