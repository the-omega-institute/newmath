import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProbeBundleFiniteMinimumFoldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProbeBundleFiniteMinimumFoldUp : Type where
  | mk (K M G P R O A B U H C Q N : BHist) : ProbeBundleFiniteMinimumFoldUp
  deriving DecidableEq

def probeBundleFiniteMinimumFoldEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: probeBundleFiniteMinimumFoldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: probeBundleFiniteMinimumFoldEncodeBHist h

def probeBundleFiniteMinimumFoldDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (probeBundleFiniteMinimumFoldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (probeBundleFiniteMinimumFoldDecodeBHist tail)

private theorem ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      probeBundleFiniteMinimumFoldDecodeBHist
        (probeBundleFiniteMinimumFoldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def probeBundleFiniteMinimumFoldFields : ProbeBundleFiniteMinimumFoldUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | ProbeBundleFiniteMinimumFoldUp.mk K M G P R O A B U H C Q N =>
      [K, M, G, P, R, O, A, B, U, H, C, Q, N]

def probeBundleFiniteMinimumFoldToEventFlow : ProbeBundleFiniteMinimumFoldUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | x => (probeBundleFiniteMinimumFoldFields x).map probeBundleFiniteMinimumFoldEncodeBHist

def probeBundleFiniteMinimumFoldEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => probeBundleFiniteMinimumFoldEventAt index rest

def probeBundleFiniteMinimumFoldFromEventFlow :
    EventFlow -> Option ProbeBundleFiniteMinimumFoldUp
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  | flow =>
      some
        (ProbeBundleFiniteMinimumFoldUp.mk
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 0 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 1 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 2 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 3 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 4 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 5 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 6 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 7 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 8 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 9 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 10 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 11 flow))
          (probeBundleFiniteMinimumFoldDecodeBHist (probeBundleFiniteMinimumFoldEventAt 12 flow)))

private theorem ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_round_trip :
    forall x : ProbeBundleFiniteMinimumFoldUp,
      probeBundleFiniteMinimumFoldFromEventFlow
        (probeBundleFiniteMinimumFoldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  intro x
  cases x with
  | mk K M G P R O A B U H C Q N =>
      change
        some
          (ProbeBundleFiniteMinimumFoldUp.mk
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist K))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist M))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist G))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist P))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist R))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist O))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist A))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist B))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist U))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist H))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist C))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist Q))
            (probeBundleFiniteMinimumFoldDecodeBHist
              (probeBundleFiniteMinimumFoldEncodeBHist N))) =
          some (ProbeBundleFiniteMinimumFoldUp.mk K M G P R O A B U H C Q N)
      rw [ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode K,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode M,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode G,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode P,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode R,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode O,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode A,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode B,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode U,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode H,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode C,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode Q,
        ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode N]

private theorem probeBundleFiniteMinimumFoldToEventFlow_injective
    {x y : ProbeBundleFiniteMinimumFoldUp} :
    probeBundleFiniteMinimumFoldToEventFlow x = probeBundleFiniteMinimumFoldToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  intro heq
  have hread :
      probeBundleFiniteMinimumFoldFromEventFlow (probeBundleFiniteMinimumFoldToEventFlow x) =
        probeBundleFiniteMinimumFoldFromEventFlow (probeBundleFiniteMinimumFoldToEventFlow y) :=
    congrArg probeBundleFiniteMinimumFoldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : ProbeBundleFiniteMinimumFoldUp,
      probeBundleFiniteMinimumFoldFields x = probeBundleFiniteMinimumFoldFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  intro x y hfields
  cases x with
  | mk K1 M1 G1 P1 R1 O1 A1 B1 U1 H1 C1 Q1 N1 =>
      cases y with
      | mk K2 M2 G2 P2 R2 O2 A2 B2 U2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance probeBundleFiniteMinimumFoldBHistCarrier :
    BHistCarrier ProbeBundleFiniteMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  toEventFlow := probeBundleFiniteMinimumFoldToEventFlow
  fromEventFlow := probeBundleFiniteMinimumFoldFromEventFlow

instance probeBundleFiniteMinimumFoldChapterTasteGate :
    ChapterTasteGate ProbeBundleFiniteMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  round_trip := by
    intro x
    change
      probeBundleFiniteMinimumFoldFromEventFlow
        (probeBundleFiniteMinimumFoldToEventFlow x) = some x
    exact ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (probeBundleFiniteMinimumFoldToEventFlow_injective heq)

instance probeBundleFiniteMinimumFoldFieldFaithful :
    FieldFaithful ProbeBundleFiniteMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  fields := probeBundleFiniteMinimumFoldFields
  field_faithful := ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_fields_faithful

instance probeBundleFiniteMinimumFoldNontrivial : Nontrivial ProbeBundleFiniteMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  witness_pair :=
    ⟨ProbeBundleFiniteMinimumFoldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ProbeBundleFiniteMinimumFoldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProbeBundleFiniteMinimumFoldUp :=
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle
  probeBundleFiniteMinimumFoldChapterTasteGate

theorem ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ProbeBundleFiniteMinimumFoldUp) ∧
      Nonempty (FieldFaithful ProbeBundleFiniteMinimumFoldUp) ∧
      Nonempty (Nontrivial ProbeBundleFiniteMinimumFoldUp) ∧
      (∀ h : BHist,
        probeBundleFiniteMinimumFoldDecodeBHist
          (probeBundleFiniteMinimumFoldEncodeBHist h) = h) ∧
      (∀ x : ProbeBundleFiniteMinimumFoldUp,
        probeBundleFiniteMinimumFoldFromEventFlow
          (probeBundleFiniteMinimumFoldToEventFlow x) = some x) ∧
      (∀ x y : ProbeBundleFiniteMinimumFoldUp,
        probeBundleFiniteMinimumFoldToEventFlow x =
          probeBundleFiniteMinimumFoldToEventFlow y -> x = y) ∧
      probeBundleFiniteMinimumFoldEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle FieldFaithful ChapterTasteGate
  exact
    ⟨⟨probeBundleFiniteMinimumFoldChapterTasteGate⟩,
      ⟨⟨probeBundleFiniteMinimumFoldFieldFaithful⟩,
        ⟨⟨probeBundleFiniteMinimumFoldNontrivial⟩,
          ⟨ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_decode,
            ⟨ProbeBundleFiniteMinimumFoldTasteGate_single_carrier_alignment_round_trip,
              ⟨fun _ _ heq => probeBundleFiniteMinimumFoldToEventFlow_injective heq,
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.ProbeBundleFiniteMinimumFoldUp
