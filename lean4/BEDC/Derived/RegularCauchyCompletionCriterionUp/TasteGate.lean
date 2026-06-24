import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionCriterionUp : Type where
  | mk (R W D M L Q H C P N : BHist) : RegularCauchyCompletionCriterionUp
  deriving DecidableEq

def regularCauchyCompletionCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionCriterionEncodeBHist h

def regularCauchyCompletionCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionCriterionDecodeBHist tail)

private theorem regularCauchyCompletionCriterionDecode_encode :
    ∀ h : BHist,
      regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionCriterionFields :
    RegularCauchyCompletionCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionCriterionUp.mk R W D M L Q H C P N =>
      [R, W, D, M, L, Q, H, C, P, N]

def regularCauchyCompletionCriterionToEventFlow :
    RegularCauchyCompletionCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionCriterionUp.mk R W D M L Q H C P N =>
      [regularCauchyCompletionCriterionEncodeBHist R,
        regularCauchyCompletionCriterionEncodeBHist W,
        regularCauchyCompletionCriterionEncodeBHist D,
        regularCauchyCompletionCriterionEncodeBHist M,
        regularCauchyCompletionCriterionEncodeBHist L,
        regularCauchyCompletionCriterionEncodeBHist Q,
        regularCauchyCompletionCriterionEncodeBHist H,
        regularCauchyCompletionCriterionEncodeBHist C,
        regularCauchyCompletionCriterionEncodeBHist P,
        regularCauchyCompletionCriterionEncodeBHist N]

private def regularCauchyCompletionCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompletionCriterionEventAt index rest

def regularCauchyCompletionCriterionFromEventFlow :
    EventFlow → Option RegularCauchyCompletionCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyCompletionCriterionUp.mk
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 0 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 1 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 2 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 3 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 4 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 5 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 6 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 7 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 8 ef))
        (regularCauchyCompletionCriterionDecodeBHist
          (regularCauchyCompletionCriterionEventAt 9 ef)))

private theorem regularCauchyCompletionCriterion_round_trip :
    ∀ x : RegularCauchyCompletionCriterionUp,
      regularCauchyCompletionCriterionFromEventFlow
          (regularCauchyCompletionCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D M L Q H C P N =>
      change
        some
            (RegularCauchyCompletionCriterionUp.mk
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist R))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist W))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist D))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist M))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist L))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist Q))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist H))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist C))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist P))
              (regularCauchyCompletionCriterionDecodeBHist
                (regularCauchyCompletionCriterionEncodeBHist N))) =
          some (RegularCauchyCompletionCriterionUp.mk R W D M L Q H C P N)
      rw [regularCauchyCompletionCriterionDecode_encode R,
        regularCauchyCompletionCriterionDecode_encode W,
        regularCauchyCompletionCriterionDecode_encode D,
        regularCauchyCompletionCriterionDecode_encode M,
        regularCauchyCompletionCriterionDecode_encode L,
        regularCauchyCompletionCriterionDecode_encode Q,
        regularCauchyCompletionCriterionDecode_encode H,
        regularCauchyCompletionCriterionDecode_encode C,
        regularCauchyCompletionCriterionDecode_encode P,
        regularCauchyCompletionCriterionDecode_encode N]

private theorem regularCauchyCompletionCriterionToEventFlow_injective
    {x y : RegularCauchyCompletionCriterionUp} :
    regularCauchyCompletionCriterionToEventFlow x =
        regularCauchyCompletionCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionCriterionFromEventFlow
          (regularCauchyCompletionCriterionToEventFlow x) =
        regularCauchyCompletionCriterionFromEventFlow
          (regularCauchyCompletionCriterionToEventFlow y) :=
    congrArg regularCauchyCompletionCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionCriterion_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionCriterion_round_trip y)))

private theorem regularCauchyCompletionCriterionFieldFaithfulProof :
    ∀ x y : RegularCauchyCompletionCriterionUp,
      regularCauchyCompletionCriterionFields x =
          regularCauchyCompletionCriterionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ D₁ M₁ L₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ D₂ M₂ L₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyCompletionCriterionBHistCarrier :
    BHistCarrier RegularCauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionCriterionToEventFlow
  fromEventFlow := regularCauchyCompletionCriterionFromEventFlow

instance regularCauchyCompletionCriterionChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionCriterionFromEventFlow
          (regularCauchyCompletionCriterionToEventFlow x) =
        some x
    exact regularCauchyCompletionCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionCriterionToEventFlow_injective heq)

instance regularCauchyCompletionCriterionFieldFaithful :
    FieldFaithful RegularCauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompletionCriterionFields
  field_faithful := regularCauchyCompletionCriterionFieldFaithfulProof

instance regularCauchyCompletionCriterionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCompletionCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyCompletionCriterionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyCompletionCriterionUp) ∧
      Nonempty (FieldFaithful RegularCauchyCompletionCriterionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyCompletionCriterionUp) ∧
      (∀ h : BHist,
        regularCauchyCompletionCriterionDecodeBHist
            (regularCauchyCompletionCriterionEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyCompletionCriterionUp,
        regularCauchyCompletionCriterionFromEventFlow
            (regularCauchyCompletionCriterionToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyCompletionCriterionUp,
        regularCauchyCompletionCriterionToEventFlow x =
            regularCauchyCompletionCriterionToEventFlow y →
          x = y) ∧
      regularCauchyCompletionCriterionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyCompletionCriterionChapterTasteGate⟩
  constructor
  · exact ⟨regularCauchyCompletionCriterionFieldFaithful⟩
  constructor
  · exact ⟨regularCauchyCompletionCriterionNontrivial⟩
  constructor
  · exact regularCauchyCompletionCriterionDecode_encode
  constructor
  · exact regularCauchyCompletionCriterion_round_trip
  constructor
  · intro x y
    exact regularCauchyCompletionCriterionToEventFlow_injective
  · rfl

theorem RegularCauchyCompletionCriterionCarrier_namecert_obligations
    {R W D M L Q H C P N windowRead toleranceRead boundaryRead : BHist} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory M →
            UnaryHistory Q →
              Cont W D windowRead →
                Cont windowRead M toleranceRead →
                  Cont toleranceRead Q boundaryRead →
                    SemanticNameCert
                        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨
                            hsame row Q ∨ hsame row boundaryRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont W D windowRead ∧
                            Cont windowRead M toleranceRead ∧
                              Cont toleranceRead Q boundaryRead)
                        hsame ∧
                      UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro _rUnary wUnary dUnary mUnary qUnary windowRoute toleranceRoute boundaryRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary mUnary toleranceRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed toleranceUnary qUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨ hsame row Q ∨
              hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧ Cont windowRead M toleranceRead ∧
              Cont toleranceRead Q boundaryRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, toleranceRoute, boundaryRoute⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, boundaryUnary⟩

end BEDC.Derived.RegularCauchyCompletionCriterionUp
