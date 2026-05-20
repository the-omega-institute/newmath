import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticResidueLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticResidueLatticeUp : Type where
  | mk : (O A M S B R K H C P N : BHist) → OnticResidueLatticeUp
  deriving DecidableEq

def onticResidueLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticResidueLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticResidueLatticeEncodeBHist h

def onticResidueLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticResidueLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticResidueLatticeDecodeBHist tail)

private theorem onticResidueLatticeDecode_encode_bhist :
    ∀ h : BHist, onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def onticResidueLatticeFields : OnticResidueLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticResidueLatticeUp.mk O A M S B R K H C P N => [O, A, M, S, B, R, K, H, C, P, N]

def onticResidueLatticeToEventFlow : OnticResidueLatticeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map onticResidueLatticeEncodeBHist (onticResidueLatticeFields x)

def onticResidueLatticeFromEventFlow : EventFlow → Option OnticResidueLatticeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [O, A, M, S, B, R, K, H, C, P, N] =>
      some
        (OnticResidueLatticeUp.mk
          (onticResidueLatticeDecodeBHist O)
          (onticResidueLatticeDecodeBHist A)
          (onticResidueLatticeDecodeBHist M)
          (onticResidueLatticeDecodeBHist S)
          (onticResidueLatticeDecodeBHist B)
          (onticResidueLatticeDecodeBHist R)
          (onticResidueLatticeDecodeBHist K)
          (onticResidueLatticeDecodeBHist H)
          (onticResidueLatticeDecodeBHist C)
          (onticResidueLatticeDecodeBHist P)
          (onticResidueLatticeDecodeBHist N))
  | _ => none

private theorem onticResidueLattice_round_trip :
    ∀ x : OnticResidueLatticeUp,
      onticResidueLatticeFromEventFlow (onticResidueLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O A M S B R K H C P N =>
      change
        some
          (OnticResidueLatticeUp.mk
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist O))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist A))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist M))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist S))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist B))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist R))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist K))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist H))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist C))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist P))
            (onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist N))) =
          some (OnticResidueLatticeUp.mk O A M S B R K H C P N)
      rw [onticResidueLatticeDecode_encode_bhist O,
        onticResidueLatticeDecode_encode_bhist A,
        onticResidueLatticeDecode_encode_bhist M,
        onticResidueLatticeDecode_encode_bhist S,
        onticResidueLatticeDecode_encode_bhist B,
        onticResidueLatticeDecode_encode_bhist R,
        onticResidueLatticeDecode_encode_bhist K,
        onticResidueLatticeDecode_encode_bhist H,
        onticResidueLatticeDecode_encode_bhist C,
        onticResidueLatticeDecode_encode_bhist P,
        onticResidueLatticeDecode_encode_bhist N]

private theorem onticResidueLatticeToEventFlow_injective {x y : OnticResidueLatticeUp} :
    onticResidueLatticeToEventFlow x = onticResidueLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticResidueLatticeFromEventFlow (onticResidueLatticeToEventFlow x) =
        onticResidueLatticeFromEventFlow (onticResidueLatticeToEventFlow y) :=
    congrArg onticResidueLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticResidueLattice_round_trip x).symm
      (Eq.trans hread (onticResidueLattice_round_trip y)))

private theorem onticResidueLattice_field_faithful :
    ∀ x y : OnticResidueLatticeUp,
      onticResidueLatticeFields x = onticResidueLatticeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk O₁ A₁ M₁ S₁ B₁ R₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ A₂ M₂ S₂ B₂ R₂ K₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance onticResidueLatticeBHistCarrier : BHistCarrier OnticResidueLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticResidueLatticeToEventFlow
  fromEventFlow := onticResidueLatticeFromEventFlow

instance onticResidueLatticeChapterTasteGate :
    ChapterTasteGate OnticResidueLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticResidueLatticeFromEventFlow (onticResidueLatticeToEventFlow x) = some x
    exact onticResidueLattice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticResidueLatticeToEventFlow_injective heq)

instance onticResidueLatticeFieldFaithful : FieldFaithful OnticResidueLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := onticResidueLatticeFields
  field_faithful := onticResidueLattice_field_faithful

instance onticResidueLatticeNontrivial : Nontrivial OnticResidueLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticResidueLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OnticResidueLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OnticResidueLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onticResidueLatticeChapterTasteGate

theorem OnticResidueLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist, onticResidueLatticeDecodeBHist (onticResidueLatticeEncodeBHist h) = h) ∧
      (∀ x : OnticResidueLatticeUp,
        onticResidueLatticeToEventFlow x =
          List.map onticResidueLatticeEncodeBHist (onticResidueLatticeFields x)) ∧
        (∀ x y : OnticResidueLatticeUp,
          onticResidueLatticeFields x = onticResidueLatticeFields y → x = y) ∧
          (∃ x y : OnticResidueLatticeUp, x ≠ y) ∧
            onticResidueLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact onticResidueLatticeDecode_encode_bhist
  constructor
  · intro x
    cases x
    rfl
  constructor
  · exact onticResidueLattice_field_faithful
  constructor
  · exact
      ⟨OnticResidueLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        OnticResidueLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩
  · rfl

theorem OnticResidueLattice_activation_nonescape {O A M S B R K H C P N : BHist} :
    onticResidueLatticeFields (OnticResidueLatticeUp.mk O A M S B R K H C P N) =
        [O, A, M, S, B, R, K, H, C, P, N] ∧
      onticResidueLatticeToEventFlow (OnticResidueLatticeUp.mk O A M S B R K H C P N) =
        List.map onticResidueLatticeEncodeBHist [O, A, M, S, B, R, K, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.OnticResidueLatticeUp
