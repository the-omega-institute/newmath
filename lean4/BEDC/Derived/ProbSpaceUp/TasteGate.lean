import BEDC.Derived.ProbSpaceUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProbSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProbSpaceUp : Type where
  | mk (omega one event complement sum : BHist) : ProbSpaceUp
  deriving DecidableEq

def probSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: probSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: probSpaceEncodeBHist h

def probSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (probSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (probSpaceDecodeBHist tail)

private theorem probSpaceDecode_encode :
    ∀ h : BHist, probSpaceDecodeBHist (probSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def probSpaceToEventFlow : ProbSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProbSpaceUp.mk omega one event complement sum =>
      [[BMark.b0],
        probSpaceEncodeBHist omega,
        [BMark.b1, BMark.b0],
        probSpaceEncodeBHist one,
        [BMark.b1, BMark.b1, BMark.b0],
        probSpaceEncodeBHist event,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        probSpaceEncodeBHist complement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        probSpaceEncodeBHist sum]

private def probSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => probSpaceEventAtDefault index rest

def probSpaceFromEventFlow (ef : EventFlow) : Option ProbSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProbSpaceUp.mk
      (probSpaceDecodeBHist (probSpaceEventAtDefault 1 ef))
      (probSpaceDecodeBHist (probSpaceEventAtDefault 3 ef))
      (probSpaceDecodeBHist (probSpaceEventAtDefault 5 ef))
      (probSpaceDecodeBHist (probSpaceEventAtDefault 7 ef))
      (probSpaceDecodeBHist (probSpaceEventAtDefault 9 ef)))

private theorem probSpace_round_trip :
    ∀ x : ProbSpaceUp, probSpaceFromEventFlow (probSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk omega one event complement sum =>
      change
        some
          (ProbSpaceUp.mk
            (probSpaceDecodeBHist (probSpaceEncodeBHist omega))
            (probSpaceDecodeBHist (probSpaceEncodeBHist one))
            (probSpaceDecodeBHist (probSpaceEncodeBHist event))
            (probSpaceDecodeBHist (probSpaceEncodeBHist complement))
            (probSpaceDecodeBHist (probSpaceEncodeBHist sum))) =
          some (ProbSpaceUp.mk omega one event complement sum)
      rw [probSpaceDecode_encode omega, probSpaceDecode_encode one,
        probSpaceDecode_encode event, probSpaceDecode_encode complement,
        probSpaceDecode_encode sum]

private theorem probSpaceToEventFlow_injective {x y : ProbSpaceUp} :
    probSpaceToEventFlow x = probSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      probSpaceFromEventFlow (probSpaceToEventFlow x) =
        probSpaceFromEventFlow (probSpaceToEventFlow y) :=
    congrArg probSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (probSpace_round_trip x).symm
      (Eq.trans hread (probSpace_round_trip y)))

instance probSpaceBHistCarrier : BHistCarrier ProbSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := probSpaceToEventFlow
  fromEventFlow := probSpaceFromEventFlow

instance probSpaceChapterTasteGate : ChapterTasteGate ProbSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change probSpaceFromEventFlow (probSpaceToEventFlow x) = some x
    exact probSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (probSpaceToEventFlow_injective heq)

instance probSpaceNontrivial : Nontrivial ProbSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProbSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProbSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProbSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  probSpaceChapterTasteGate

theorem ProbSpaceMeasureDependencyRoute {omega one event complement sum : BHist} :
    ProbSpacePublicEventPacket omega one event complement sum ->
      SemanticNameCert
          (fun row : BHist =>
            (hsame row event ∨ hsame row complement ∨ hsame row sum) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row event ∨ hsame row complement ∨ hsame row sum ∨
              hsame row omega ∨ hsame row one)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont event complement sum ∧ hsame omega one ∧
              hsame omega sum)
          hsame ∧
        UnaryHistory event ∧ UnaryHistory complement ∧ Cont event complement sum ∧
          hsame omega one ∧ hsame omega sum := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨eventUnary, complementUnary, eventComplementSum, omegaOne, omegaSum⟩ := packet
  have sumUnary : UnaryHistory sum :=
    unary_cont_closed eventUnary complementUnary eventComplementSum
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row event ∨ hsame row complement ∨ hsame row sum) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row event ∨ hsame row complement ∨ hsame row sum ∨
              hsame row omega ∨ hsame row one)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont event complement sum ∧ hsame omega one ∧
              hsame omega sum)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro event ⟨Or.inl (hsame_refl event), eventUnary⟩
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
        constructor
        · cases source.left with
          | inl eventSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) eventSame)
          | inr rest =>
              cases rest with
              | inl complementSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) complementSame))
              | inr sumSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sumSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl eventSame =>
          exact Or.inl eventSame
      | inr rest =>
          cases rest with
          | inl complementSame =>
              exact Or.inr (Or.inl complementSame)
          | inr sumSame =>
              exact Or.inr (Or.inr (Or.inl sumSame))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, eventComplementSum, omegaOne, omegaSum⟩
  }
  exact ⟨cert, eventUnary, complementUnary, eventComplementSum, omegaOne, omegaSum⟩

end BEDC.Derived.ProbSpaceUp
