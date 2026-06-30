import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformlyContinuousCompletionExtensionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformlyContinuousCompletionExtensionUp : Type where
  | mk (D T M L U R S Y E H C P N : BHist) : UniformlyContinuousCompletionExtensionUp
  deriving DecidableEq

def uniformlyContinuousCompletionExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformlyContinuousCompletionExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformlyContinuousCompletionExtensionEncodeBHist h

def uniformlyContinuousCompletionExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformlyContinuousCompletionExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformlyContinuousCompletionExtensionDecodeBHist tail)

theorem UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment :
    ∀ h : BHist,
      uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformlyContinuousCompletionExtensionFields :
    UniformlyContinuousCompletionExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformlyContinuousCompletionExtensionUp.mk D T M L U R S Y E H C P N =>
      [D, T, M, L, U, R, S, Y, E, H, C, P, N]

def uniformlyContinuousCompletionExtensionToEventFlow :
    UniformlyContinuousCompletionExtensionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (uniformlyContinuousCompletionExtensionFields x).map
      uniformlyContinuousCompletionExtensionEncodeBHist

private def uniformlyContinuousCompletionExtensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformlyContinuousCompletionExtensionEventAtDefault index rest

def uniformlyContinuousCompletionExtensionFromEventFlow
    (ef : EventFlow) : Option UniformlyContinuousCompletionExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformlyContinuousCompletionExtensionUp.mk
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 0 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 1 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 2 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 3 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 4 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 5 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 6 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 7 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 8 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 9 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 10 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 11 ef))
      (uniformlyContinuousCompletionExtensionDecodeBHist
        (uniformlyContinuousCompletionExtensionEventAtDefault 12 ef)))

private theorem UniformlyContinuousCompletionExtensionTasteGate_round_trip :
    ∀ x : UniformlyContinuousCompletionExtensionUp,
      uniformlyContinuousCompletionExtensionFromEventFlow
        (uniformlyContinuousCompletionExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D T M L U R S Y E H C P N =>
      change
        some
          (UniformlyContinuousCompletionExtensionUp.mk
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist D))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist T))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist M))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist L))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist U))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist R))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist S))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist Y))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist E))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist H))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist C))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist P))
            (uniformlyContinuousCompletionExtensionDecodeBHist
              (uniformlyContinuousCompletionExtensionEncodeBHist N))) =
          some (UniformlyContinuousCompletionExtensionUp.mk D T M L U R S Y E H C P N)
      rw [UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment D,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment T,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment M,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment L,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment U,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment R,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment S,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment Y,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment E,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment H,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment C,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment P,
        UniformlyContinuousCompletionExtensionTasteGate_single_carrier_alignment N]

private theorem UniformlyContinuousCompletionExtensionTasteGate_toEventFlow_injective
    {x y : UniformlyContinuousCompletionExtensionUp} :
    uniformlyContinuousCompletionExtensionToEventFlow x =
      uniformlyContinuousCompletionExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformlyContinuousCompletionExtensionFromEventFlow
          (uniformlyContinuousCompletionExtensionToEventFlow x) =
        uniformlyContinuousCompletionExtensionFromEventFlow
          (uniformlyContinuousCompletionExtensionToEventFlow y) :=
    congrArg uniformlyContinuousCompletionExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformlyContinuousCompletionExtensionTasteGate_round_trip x).symm
      (Eq.trans hread (UniformlyContinuousCompletionExtensionTasteGate_round_trip y)))

instance uniformlyContinuousCompletionExtensionBHistCarrier :
    BHistCarrier UniformlyContinuousCompletionExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformlyContinuousCompletionExtensionToEventFlow
  fromEventFlow := uniformlyContinuousCompletionExtensionFromEventFlow

instance uniformlyContinuousCompletionExtensionChapterTasteGate :
    ChapterTasteGate UniformlyContinuousCompletionExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformlyContinuousCompletionExtensionFromEventFlow
        (uniformlyContinuousCompletionExtensionToEventFlow x) = some x
    exact UniformlyContinuousCompletionExtensionTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformlyContinuousCompletionExtensionTasteGate_toEventFlow_injective heq)

theorem UniformlyContinuousCompletionExtension_modulus_handoff_route
    {D T M L U R S Y E H C P N : BHist}
    (hDTM : Cont D T M) (hMLU : Cont M L U) (hURS : Cont U R S)
    (hSYE : Cont S Y E) (hEHC : Cont E H C) (hCPN : Cont C P N) :
    (∃ route : BHist,
        route = N ∧ Cont D T M ∧ Cont M L U ∧ Cont U R S ∧ Cont S Y E ∧
          Cont E H C ∧ Cont C P route) ∧
      SemanticNameCert
        (fun row : BHist => row = M ∧ Cont D T M)
        (fun row : BHist => row = M ∨ row = L ∨ row = U ∨ row = R ∨
          row = S ∨ row = Y ∨ row = E)
        (fun row : BHist => hsame row M ∨ hsame row E ∨ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  constructor
  · exact ⟨N, rfl, hDTM, hMLU, hURS, hSYE, hEHC, hCPN⟩
  · have sourceM :
        (fun row : BHist => row = M ∧ Cont D T M) M := by
      exact ⟨rfl, hDTM⟩
    exact {
      core := {
        carrier_inhabited := Exists.intro M sourceM
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          constructor
          · exact hsame_trans (hsame_symm same) source.left
          · exact hDTM
      }
      pattern_sound := by
        intro _row source
        exact Or.inl source.left
      ledger_sound := by
        intro _row source
        exact Or.inl source.left
    }

end BEDC.Derived.UniformlyContinuousCompletionExtensionUp.TasteGate
