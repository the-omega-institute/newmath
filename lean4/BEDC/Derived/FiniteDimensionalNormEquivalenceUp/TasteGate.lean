import BEDC.Derived.FiniteDimensionalNormEquivalenceUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDimensionalNormEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDimensionalNormEquivalenceUp : Type where
  | mk (V K A B R L U H T P N : BHist) : FiniteDimensionalNormEquivalenceUp
  deriving DecidableEq

def finiteDimensionalNormEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDimensionalNormEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDimensionalNormEquivalenceEncodeBHist h

def finiteDimensionalNormEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDimensionalNormEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDimensionalNormEquivalenceDecodeBHist tail)

private theorem finiteDimensionalNormEquivalence_decode_encode :
    ∀ h : BHist,
      finiteDimensionalNormEquivalenceDecodeBHist
          (finiteDimensionalNormEquivalenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDimensionalNormEquivalenceFields :
    FiniteDimensionalNormEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalNormEquivalenceUp.mk V K A B R L U H T P N =>
      [V, K, A, B, R, L, U, H, T, P, N]

def finiteDimensionalNormEquivalenceToEventFlow :
    FiniteDimensionalNormEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (finiteDimensionalNormEquivalenceFields x).map
        finiteDimensionalNormEquivalenceEncodeBHist

private def finiteDimensionalNormEquivalenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => finiteDimensionalNormEquivalenceRawAt index rest

def finiteDimensionalNormEquivalenceFromEventFlow
    (flow : EventFlow) : Option FiniteDimensionalNormEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDimensionalNormEquivalenceUp.mk
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 0 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 1 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 2 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 3 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 4 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 5 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 6 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 7 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 8 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 9 flow))
      (finiteDimensionalNormEquivalenceDecodeBHist
        (finiteDimensionalNormEquivalenceRawAt 10 flow)))

private theorem finiteDimensionalNormEquivalence_round_trip
    (x : FiniteDimensionalNormEquivalenceUp) :
    finiteDimensionalNormEquivalenceFromEventFlow
        (finiteDimensionalNormEquivalenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk V K A B R L U H T P N =>
      change
        some
          (FiniteDimensionalNormEquivalenceUp.mk
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist V))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist K))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist A))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist B))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist R))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist L))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist U))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist H))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist T))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist P))
            (finiteDimensionalNormEquivalenceDecodeBHist
              (finiteDimensionalNormEquivalenceEncodeBHist N))) =
          some (FiniteDimensionalNormEquivalenceUp.mk V K A B R L U H T P N)
      rw [finiteDimensionalNormEquivalence_decode_encode V,
        finiteDimensionalNormEquivalence_decode_encode K,
        finiteDimensionalNormEquivalence_decode_encode A,
        finiteDimensionalNormEquivalence_decode_encode B,
        finiteDimensionalNormEquivalence_decode_encode R,
        finiteDimensionalNormEquivalence_decode_encode L,
        finiteDimensionalNormEquivalence_decode_encode U,
        finiteDimensionalNormEquivalence_decode_encode H,
        finiteDimensionalNormEquivalence_decode_encode T,
        finiteDimensionalNormEquivalence_decode_encode P,
        finiteDimensionalNormEquivalence_decode_encode N]

private theorem finiteDimensionalNormEquivalenceToEventFlow_injective
    {x y : FiniteDimensionalNormEquivalenceUp} :
    finiteDimensionalNormEquivalenceToEventFlow x =
        finiteDimensionalNormEquivalenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDimensionalNormEquivalenceFromEventFlow
          (finiteDimensionalNormEquivalenceToEventFlow x) =
        finiteDimensionalNormEquivalenceFromEventFlow
          (finiteDimensionalNormEquivalenceToEventFlow y) :=
    congrArg finiteDimensionalNormEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteDimensionalNormEquivalence_round_trip x).symm
      (Eq.trans hread (finiteDimensionalNormEquivalence_round_trip y)))

instance finiteDimensionalNormEquivalenceBHistCarrier :
    BHistCarrier FiniteDimensionalNormEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDimensionalNormEquivalenceToEventFlow
  fromEventFlow := finiteDimensionalNormEquivalenceFromEventFlow

instance finiteDimensionalNormEquivalenceChapterTasteGate :
    ChapterTasteGate FiniteDimensionalNormEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDimensionalNormEquivalenceFromEventFlow
          (finiteDimensionalNormEquivalenceToEventFlow x) =
        some x
    exact finiteDimensionalNormEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteDimensionalNormEquivalenceToEventFlow_injective heq)

instance finiteDimensionalNormEquivalenceFieldFaithful :
    FieldFaithful FiniteDimensionalNormEquivalenceUp where
  fields := finiteDimensionalNormEquivalenceFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk V1 K1 A1 B1 R1 L1 U1 H1 T1 P1 N1 =>
      cases y with
      | mk V2 K2 A2 B2 R2 L2 U2 H2 T2 P2 N2 =>
        injection h with hV tK
        injection tK with hK tA
        injection tA with hA tB
        injection tB with hB tR
        injection tR with hR tL
        injection tL with hL tU
        injection tU with hU tH
        injection tH with hH tT
        injection tT with hT tP
        injection tP with hP tN
        injection tN with hN _
        subst hV
        subst hK
        subst hA
        subst hB
        subst hR
        subst hL
        subst hU
        subst hH
        subst hT
        subst hP
        subst hN
        rfl

instance finiteDimensionalNormEquivalenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteDimensionalNormEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDimensionalNormEquivalenceUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteDimensionalNormEquivalenceUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with impossible
        cases impossible⟩

theorem FiniteDimensionalNormEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteDimensionalNormEquivalenceDecodeBHist
          (finiteDimensionalNormEquivalenceEncodeBHist h) =
        h) ∧
      (∀ x : FiniteDimensionalNormEquivalenceUp,
        finiteDimensionalNormEquivalenceFromEventFlow
            (finiteDimensionalNormEquivalenceToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteDimensionalNormEquivalenceUp,
          finiteDimensionalNormEquivalenceToEventFlow x =
              finiteDimensionalNormEquivalenceToEventFlow y →
            x = y) ∧
          finiteDimensionalNormEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact finiteDimensionalNormEquivalence_decode_encode
  constructor
  · exact finiteDimensionalNormEquivalence_round_trip
  constructor
  · intro x y heq
    exact finiteDimensionalNormEquivalenceToEventFlow_injective heq
  · rfl

end BEDC.Derived.FiniteDimensionalNormEquivalenceUp
