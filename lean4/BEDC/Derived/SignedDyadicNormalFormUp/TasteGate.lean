import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDyadicNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDyadicNormalFormUp : Type where
  | mk (M E L C K D T H R P N : BHist) : SignedDyadicNormalFormUp
  deriving DecidableEq

def signedDyadicNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDyadicNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDyadicNormalFormEncodeBHist h

def signedDyadicNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDyadicNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDyadicNormalFormDecodeBHist tail)

private theorem signedDyadicNormalFormDecode_encode :
    ∀ h : BHist,
      signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedDyadicNormalFormFields : SignedDyadicNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDyadicNormalFormUp.mk M E L C K D T H R P N =>
      [M, E, L, C, K, D, T, H, R, P, N]

def signedDyadicNormalFormToEventFlow : SignedDyadicNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (signedDyadicNormalFormFields x).map signedDyadicNormalFormEncodeBHist

private def signedDyadicNormalFormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => signedDyadicNormalFormEventAt index rest

def signedDyadicNormalFormFromEventFlow
    (ef : EventFlow) : Option SignedDyadicNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SignedDyadicNormalFormUp.mk
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 0 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 1 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 2 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 3 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 4 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 5 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 6 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 7 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 8 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 9 ef))
      (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEventAt 10 ef)))

private theorem signedDyadicNormalForm_round_trip (x : SignedDyadicNormalFormUp) :
    signedDyadicNormalFormFromEventFlow (signedDyadicNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M E L C K D T H R P N =>
      change
        some
          (SignedDyadicNormalFormUp.mk
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist M))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist E))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist L))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist C))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist K))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist D))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist T))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist H))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist R))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist P))
            (signedDyadicNormalFormDecodeBHist (signedDyadicNormalFormEncodeBHist N))) =
          some (SignedDyadicNormalFormUp.mk M E L C K D T H R P N)
      rw [signedDyadicNormalFormDecode_encode M, signedDyadicNormalFormDecode_encode E,
        signedDyadicNormalFormDecode_encode L, signedDyadicNormalFormDecode_encode C,
        signedDyadicNormalFormDecode_encode K, signedDyadicNormalFormDecode_encode D,
        signedDyadicNormalFormDecode_encode T, signedDyadicNormalFormDecode_encode H,
        signedDyadicNormalFormDecode_encode R, signedDyadicNormalFormDecode_encode P,
        signedDyadicNormalFormDecode_encode N]

private theorem signedDyadicNormalFormToEventFlow_injective
    {x y : SignedDyadicNormalFormUp} :
    signedDyadicNormalFormToEventFlow x = signedDyadicNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDyadicNormalFormFromEventFlow (signedDyadicNormalFormToEventFlow x) =
        signedDyadicNormalFormFromEventFlow (signedDyadicNormalFormToEventFlow y) :=
    congrArg signedDyadicNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (signedDyadicNormalForm_round_trip x).symm
      (Eq.trans hread (signedDyadicNormalForm_round_trip y)))

private theorem signedDyadicNormalFormFields_faithful :
    ∀ x y : SignedDyadicNormalFormUp,
      signedDyadicNormalFormFields x = signedDyadicNormalFormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ E₁ L₁ C₁ K₁ D₁ T₁ H₁ R₁ P₁ N₁ =>
      cases y with
      | mk M₂ E₂ L₂ C₂ K₂ D₂ T₂ H₂ R₂ P₂ N₂ =>
          injection hfields with hM tail0
          injection tail0 with hE tail1
          injection tail1 with hL tail2
          injection tail2 with hC tail3
          injection tail3 with hK tail4
          injection tail4 with hD tail5
          injection tail5 with hT tail6
          injection tail6 with hH tail7
          injection tail7 with hR tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hM
          subst hE
          subst hL
          subst hC
          subst hK
          subst hD
          subst hT
          subst hH
          subst hR
          subst hP
          subst hN
          rfl

instance signedDyadicNormalFormBHistCarrier :
    BHistCarrier SignedDyadicNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDyadicNormalFormToEventFlow
  fromEventFlow := signedDyadicNormalFormFromEventFlow

instance signedDyadicNormalFormChapterTasteGate :
    ChapterTasteGate SignedDyadicNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      signedDyadicNormalFormFromEventFlow (signedDyadicNormalFormToEventFlow x) = some x
    exact signedDyadicNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (signedDyadicNormalFormToEventFlow_injective heq)

instance signedDyadicNormalFormFieldFaithful :
    FieldFaithful SignedDyadicNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := signedDyadicNormalFormFields
  field_faithful := signedDyadicNormalFormFields_faithful

instance signedDyadicNormalFormNontrivial : Nontrivial SignedDyadicNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SignedDyadicNormalFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SignedDyadicNormalFormUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def signedDyadicNormalFormTasteGate : ChapterTasteGate SignedDyadicNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  signedDyadicNormalFormChapterTasteGate

theorem SignedDyadicNormalFormTasteGate_single_carrier_alignment :
    (∀ x : SignedDyadicNormalFormUp,
      signedDyadicNormalFormFromEventFlow (signedDyadicNormalFormToEventFlow x) = some x) ∧
      (∀ x y : SignedDyadicNormalFormUp,
        signedDyadicNormalFormToEventFlow x = signedDyadicNormalFormToEventFlow y → x = y) ∧
        signedDyadicNormalFormFields
            (SignedDyadicNormalFormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact signedDyadicNormalForm_round_trip x
  · constructor
    · intro x y heq
      exact signedDyadicNormalFormToEventFlow_injective heq
    · rfl

end BEDC.Derived.SignedDyadicNormalFormUp
