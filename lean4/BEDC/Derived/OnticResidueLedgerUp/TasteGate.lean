import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticResidueLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticResidueLedgerUp : Type where
  | mk (O M S A C R H T P N : BHist) : OnticResidueLedgerUp
  deriving DecidableEq

def onticResidueLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticResidueLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticResidueLedgerEncodeBHist h

def onticResidueLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticResidueLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticResidueLedgerDecodeBHist tail)

private theorem onticResidueLedgerDecode_encode_bhist :
    ∀ h : BHist,
      onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def onticResidueLedgerFields : OnticResidueLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticResidueLedgerUp.mk O M S A C R H T P N => [O, M, S, A, C, R, H, T, P, N]

def onticResidueLedgerToEventFlow : OnticResidueLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (onticResidueLedgerFields x).map onticResidueLedgerEncodeBHist

def onticResidueLedgerFromEventFlow : EventFlow → Option OnticResidueLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | O :: M :: S :: A :: C :: R :: H :: T :: P :: N :: [] =>
      some
        (OnticResidueLedgerUp.mk
          (onticResidueLedgerDecodeBHist O)
          (onticResidueLedgerDecodeBHist M)
          (onticResidueLedgerDecodeBHist S)
          (onticResidueLedgerDecodeBHist A)
          (onticResidueLedgerDecodeBHist C)
          (onticResidueLedgerDecodeBHist R)
          (onticResidueLedgerDecodeBHist H)
          (onticResidueLedgerDecodeBHist T)
          (onticResidueLedgerDecodeBHist P)
          (onticResidueLedgerDecodeBHist N))
  | _ => none

private theorem onticResidueLedger_round_trip :
    ∀ x : OnticResidueLedgerUp,
      onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O M S A C R H T P N =>
      change
        some
          (OnticResidueLedgerUp.mk
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist O))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist M))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist S))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist A))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist C))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist R))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist H))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist T))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist P))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist N))) =
          some (OnticResidueLedgerUp.mk O M S A C R H T P N)
      rw [onticResidueLedgerDecode_encode_bhist O, onticResidueLedgerDecode_encode_bhist M,
        onticResidueLedgerDecode_encode_bhist S, onticResidueLedgerDecode_encode_bhist A,
        onticResidueLedgerDecode_encode_bhist C, onticResidueLedgerDecode_encode_bhist R,
        onticResidueLedgerDecode_encode_bhist H, onticResidueLedgerDecode_encode_bhist T,
        onticResidueLedgerDecode_encode_bhist P, onticResidueLedgerDecode_encode_bhist N]

private theorem onticResidueLedgerToEventFlow_injective
    {x y : OnticResidueLedgerUp} :
    onticResidueLedgerToEventFlow x = onticResidueLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) =
        onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow y) :=
    congrArg onticResidueLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticResidueLedger_round_trip x).symm
      (Eq.trans hread (onticResidueLedger_round_trip y)))

private theorem onticResidueLedger_fields_faithful :
    ∀ x y : OnticResidueLedgerUp,
      onticResidueLedgerFields x = onticResidueLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ M₁ S₁ A₁ C₁ R₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk O₂ M₂ S₂ A₂ C₂ R₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance onticResidueLedgerBHistCarrier : BHistCarrier OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticResidueLedgerToEventFlow
  fromEventFlow := onticResidueLedgerFromEventFlow

instance onticResidueLedgerChapterTasteGate :
    ChapterTasteGate OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) = some x
    exact onticResidueLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticResidueLedgerToEventFlow_injective heq)

instance onticResidueLedgerFieldFaithful : FieldFaithful OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := onticResidueLedgerFields
  field_faithful := onticResidueLedger_fields_faithful

instance onticResidueLedgerNontrivial : Nontrivial OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OnticResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onticResidueLedgerChapterTasteGate

theorem OnticResidueLedgerTasteGate_single_carrier_alignment :
    (∃ x y : OnticResidueLedgerUp, x ≠ y) ∧
      (∀ x y : OnticResidueLedgerUp,
        onticResidueLedgerFields x = onticResidueLedgerFields y → x = y) ∧
        onticResidueLedgerToEventFlow
            (OnticResidueLedgerUp.mk BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist (BHist.e0 BHist.Empty),
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty,
            onticResidueLedgerEncodeBHist BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact
      ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩
  · constructor
    · exact onticResidueLedger_fields_faithful
    · rfl

end BEDC.Derived.OnticResidueLedgerUp
