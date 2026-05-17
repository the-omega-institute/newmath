import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProgrammeStrengthGradientLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProgrammeStrengthGradientLedgerUp : Type where
  | mk : (Q L T F B M V D U E R H C P N : BHist) → ProgrammeStrengthGradientLedgerUp
  deriving DecidableEq

def programmeStrengthGradientLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: programmeStrengthGradientLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: programmeStrengthGradientLedgerEncodeBHist h

def programmeStrengthGradientLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (programmeStrengthGradientLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (programmeStrengthGradientLedgerDecodeBHist tail)

theorem ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem programmeStrengthGradientLedger_mk_congr
    {Q Q' L L' T T' F F' B B' M M' V V' D D' U U' E E' R R' H H'
      C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hL : L' = L) (hT : T' = T) (hF : F' = F) (hB : B' = B)
    (hM : M' = M) (hV : V' = V) (hD : D' = D) (hU : U' = U) (hE : E' = E)
    (hR : R' = R) (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ProgrammeStrengthGradientLedgerUp.mk Q' L' T' F' B' M' V' D' U' E' R' H' C' P' N' =
      ProgrammeStrengthGradientLedgerUp.mk Q L T F B M V D U E R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hL
  cases hT
  cases hF
  cases hB
  cases hM
  cases hV
  cases hD
  cases hU
  cases hE
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def programmeStrengthGradientLedgerToEventFlow :
    ProgrammeStrengthGradientLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProgrammeStrengthGradientLedgerUp.mk Q L T F B M V D U E R H C P N =>
      [[BMark.b1, BMark.b0, BMark.b0],
        programmeStrengthGradientLedgerEncodeBHist Q,
        programmeStrengthGradientLedgerEncodeBHist L,
        programmeStrengthGradientLedgerEncodeBHist T,
        programmeStrengthGradientLedgerEncodeBHist F,
        programmeStrengthGradientLedgerEncodeBHist B,
        programmeStrengthGradientLedgerEncodeBHist M,
        programmeStrengthGradientLedgerEncodeBHist V,
        programmeStrengthGradientLedgerEncodeBHist D,
        programmeStrengthGradientLedgerEncodeBHist U,
        programmeStrengthGradientLedgerEncodeBHist E,
        programmeStrengthGradientLedgerEncodeBHist R,
        programmeStrengthGradientLedgerEncodeBHist H,
        programmeStrengthGradientLedgerEncodeBHist C,
        programmeStrengthGradientLedgerEncodeBHist P,
        programmeStrengthGradientLedgerEncodeBHist N]

private def programmeStrengthGradientLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => programmeStrengthGradientLedgerEventAtDefault index rest

def programmeStrengthGradientLedgerFromEventFlow :
    EventFlow → Option ProgrammeStrengthGradientLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ProgrammeStrengthGradientLedgerUp.mk
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 1 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 2 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 3 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 4 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 5 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 6 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 7 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 8 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 9 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 10 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 11 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 12 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 13 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 14 ef))
        (programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEventAtDefault 15 ef)))

def programmeStrengthGradientLedgerFields :
    ProgrammeStrengthGradientLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProgrammeStrengthGradientLedgerUp.mk Q L T F B M V D U E R H C P N =>
      [Q, L, T, F, B, M, V, D, U, E, R, H, C, P, N]

theorem ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProgrammeStrengthGradientLedgerUp,
      programmeStrengthGradientLedgerFromEventFlow
          (programmeStrengthGradientLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q L T F B M V D U E R H C P N =>
      change
        some
          (ProgrammeStrengthGradientLedgerUp.mk
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist Q))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist L))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist T))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist F))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist B))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist M))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist V))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist D))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist U))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist E))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist R))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist H))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist C))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist P))
            (programmeStrengthGradientLedgerDecodeBHist
              (programmeStrengthGradientLedgerEncodeBHist N))) =
          some (ProgrammeStrengthGradientLedgerUp.mk Q L T F B M V D U E R H C P N)
      rw [ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode Q,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode L,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode T,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode F,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode B,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode M,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode V,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode D,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode U,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode E,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode R,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode H,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode C,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode P,
        ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode N]

theorem ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_injective
    {x y : ProgrammeStrengthGradientLedgerUp} :
    programmeStrengthGradientLedgerToEventFlow x =
        programmeStrengthGradientLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      programmeStrengthGradientLedgerFromEventFlow
          (programmeStrengthGradientLedgerToEventFlow x) =
        programmeStrengthGradientLedgerFromEventFlow
          (programmeStrengthGradientLedgerToEventFlow y) :=
    congrArg programmeStrengthGradientLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem programmeStrengthGradientLedger_field_faithful :
    ∀ x y : ProgrammeStrengthGradientLedgerUp,
      programmeStrengthGradientLedgerFields x =
          programmeStrengthGradientLedgerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Q₁ L₁ T₁ F₁ B₁ M₁ V₁ D₁ U₁ E₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ L₂ T₂ F₂ B₂ M₂ V₂ D₂ U₂ E₂ R₂ H₂ C₂ P₂ N₂ =>
          injection h with hQ t1
          injection t1 with hL t2
          injection t2 with hT t3
          injection t3 with hF t4
          injection t4 with hB t5
          injection t5 with hM t6
          injection t6 with hV t7
          injection t7 with hD t8
          injection t8 with hU t9
          injection t9 with hE t10
          injection t10 with hR t11
          injection t11 with hH t12
          injection t12 with hC t13
          injection t13 with hP t14
          injection t14 with hN _
          cases hQ
          cases hL
          cases hT
          cases hF
          cases hB
          cases hM
          cases hV
          cases hD
          cases hU
          cases hE
          cases hR
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance programmeStrengthGradientLedgerBHistCarrier :
    BHistCarrier ProgrammeStrengthGradientLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := programmeStrengthGradientLedgerToEventFlow
  fromEventFlow := programmeStrengthGradientLedgerFromEventFlow

instance programmeStrengthGradientLedgerChapterTasteGate :
    ChapterTasteGate ProgrammeStrengthGradientLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      programmeStrengthGradientLedgerFromEventFlow
          (programmeStrengthGradientLedgerToEventFlow x) =
        some x
    exact ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_injective heq)

instance programmeStrengthGradientLedgerFieldFaithful :
    FieldFaithful ProgrammeStrengthGradientLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := programmeStrengthGradientLedgerFields
  field_faithful := programmeStrengthGradientLedger_field_faithful

instance programmeStrengthGradientLedgerNontrivial :
    Nontrivial ProgrammeStrengthGradientLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProgrammeStrengthGradientLedgerUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ProgrammeStrengthGradientLedgerUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProgrammeStrengthGradientLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  programmeStrengthGradientLedgerChapterTasteGate

def taste_gate_witness : FieldFaithful ProgrammeStrengthGradientLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  programmeStrengthGradientLedgerFieldFaithful

theorem ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      programmeStrengthGradientLedgerDecodeBHist
          (programmeStrengthGradientLedgerEncodeBHist h) =
        h) ∧
      (∀ x : ProgrammeStrengthGradientLedgerUp,
        programmeStrengthGradientLedgerFromEventFlow
            (programmeStrengthGradientLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : ProgrammeStrengthGradientLedgerUp,
          programmeStrengthGradientLedgerToEventFlow x =
              programmeStrengthGradientLedgerToEventFlow y →
            x = y) ∧
          programmeStrengthGradientLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ProgrammeStrengthGradientLedgerTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ProgrammeStrengthGradientLedgerUp
