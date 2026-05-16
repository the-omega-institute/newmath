import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompressionLedgerFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompressionLedgerFunctorUp : Type where
  | mk : (A K E R O M L Q J H C P N : BHist) → CompressionLedgerFunctorUp
  deriving DecidableEq

def compressionLedgerFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compressionLedgerFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compressionLedgerFunctorEncodeBHist h

def compressionLedgerFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compressionLedgerFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compressionLedgerFunctorDecodeBHist tail)

private theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compressionLedgerFunctorFields : CompressionLedgerFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N =>
      [A, K, E, R, O, M, L, Q, J, H, C, P, N]

def compressionLedgerFunctorToEventFlow : CompressionLedgerFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N =>
      [[BMark.b0],
        compressionLedgerFunctorEncodeBHist A,
        [BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compressionLedgerFunctorEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist N]

private def CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault index rest

def compressionLedgerFunctorFromEventFlow
    (ef : EventFlow) : Option CompressionLedgerFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompressionLedgerFunctorUp.mk
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 17 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 19 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 21 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 23 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 25 ef)))

private theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompressionLedgerFunctorUp,
      compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) = some x :=
    by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A K E R O M L Q J H C P N =>
      change
        some
          (CompressionLedgerFunctorUp.mk
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist A))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist K))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist E))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist R))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist O))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist M))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist L))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist Q))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist J))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist H))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist C))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist P))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist N))) =
          some (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N)
      rw [CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode A,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode K,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode E,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode R,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode O,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode M,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode L,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode Q,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode J,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode H,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode C,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode P,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode N]

private theorem CompressionLedgerFunctorToEventFlow_injective
    {x y : CompressionLedgerFunctorUp} :
    compressionLedgerFunctorToEventFlow x = compressionLedgerFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) =
        compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow y) :=
    congrArg compressionLedgerFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompressionLedgerFunctorUp,
      compressionLedgerFunctorFields x = compressionLedgerFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ K₁ E₁ R₁ O₁ M₁ L₁ Q₁ J₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ K₂ E₂ R₂ O₂ M₂ L₂ Q₂ J₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compressionLedgerFunctorBHistCarrier : BHistCarrier CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compressionLedgerFunctorToEventFlow
  fromEventFlow := compressionLedgerFunctorFromEventFlow

instance compressionLedgerFunctorChapterTasteGate :
    ChapterTasteGate CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) = some x
    exact CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompressionLedgerFunctorToEventFlow_injective heq)

instance compressionLedgerFunctorFieldFaithful : FieldFaithful CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compressionLedgerFunctorFields
  field_faithful := CompressionLedgerFunctorTasteGate_single_carrier_alignment_fields

instance compressionLedgerFunctorNontrivial : Nontrivial CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompressionLedgerFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compressionLedgerFunctorChapterTasteGate

theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment :
    Nonempty (Nontrivial CompressionLedgerFunctorUp) ∧
      Nonempty (FieldFaithful CompressionLedgerFunctorUp) ∧
        Nonempty (ChapterTasteGate CompressionLedgerFunctorUp) ∧
          BHistCarrier.toEventFlow
              (CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty) ≠
            BHistCarrier.toEventFlow
              (CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨compressionLedgerFunctorNontrivial⟩
  · constructor
    · exact ⟨compressionLedgerFunctorFieldFaithful⟩
    · constructor
      · exact ⟨compressionLedgerFunctorChapterTasteGate⟩
      · intro heq
        have hxy :=
          CompressionLedgerFunctorToEventFlow_injective
            (x := CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            (y := CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            heq
        cases hxy

end BEDC.Derived.CompressionLedgerFunctorUp
