import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCompletionExtensionModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactCompletionExtensionModulusUp : Type where
  | mk (Q G B M L R S D E H C P N : BHist) : CompactCompletionExtensionModulusUp
  deriving DecidableEq

def compactCompletionExtensionModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCompletionExtensionModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCompletionExtensionModulusEncodeBHist h

def compactCompletionExtensionModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCompletionExtensionModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCompletionExtensionModulusDecodeBHist tail)

theorem CompactCompletionExtensionModulusTasteGate_single_carrier_alignment :
    ∀ h : BHist,
      compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def compactCompletionExtensionModulusFields :
    CompactCompletionExtensionModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactCompletionExtensionModulusUp.mk Q G B M L R S D E H C P N =>
      [Q, G, B, M, L, R, S, D, E, H, C, P, N]

def compactCompletionExtensionModulusToEventFlow :
    CompactCompletionExtensionModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (compactCompletionExtensionModulusFields x).map
      compactCompletionExtensionModulusEncodeBHist

private def compactCompletionExtensionModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactCompletionExtensionModulusEventAtDefault index rest

def compactCompletionExtensionModulusFromEventFlow
    (ef : EventFlow) : Option CompactCompletionExtensionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactCompletionExtensionModulusUp.mk
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 0 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 1 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 2 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 3 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 4 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 5 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 6 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 7 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 8 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 9 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 10 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 11 ef))
      (compactCompletionExtensionModulusDecodeBHist
        (compactCompletionExtensionModulusEventAtDefault 12 ef)))

private theorem CompactCompletionExtensionModulusTasteGate_round_trip :
    ∀ x : CompactCompletionExtensionModulusUp,
      compactCompletionExtensionModulusFromEventFlow
        (compactCompletionExtensionModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q G B M L R S D E H C P N =>
      change
        some
          (CompactCompletionExtensionModulusUp.mk
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist Q))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist G))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist B))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist M))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist L))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist R))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist S))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist D))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist E))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist H))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist C))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist P))
            (compactCompletionExtensionModulusDecodeBHist
              (compactCompletionExtensionModulusEncodeBHist N))) =
          some (CompactCompletionExtensionModulusUp.mk Q G B M L R S D E H C P N)
      rw [CompactCompletionExtensionModulusTasteGate_single_carrier_alignment Q,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment G,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment B,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment M,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment L,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment R,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment S,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment D,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment E,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment H,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment C,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment P,
        CompactCompletionExtensionModulusTasteGate_single_carrier_alignment N]

private theorem CompactCompletionExtensionModulusTasteGate_toEventFlow_injective
    {x y : CompactCompletionExtensionModulusUp} :
    compactCompletionExtensionModulusToEventFlow x =
      compactCompletionExtensionModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactCompletionExtensionModulusFromEventFlow
          (compactCompletionExtensionModulusToEventFlow x) =
        compactCompletionExtensionModulusFromEventFlow
          (compactCompletionExtensionModulusToEventFlow y) :=
    congrArg compactCompletionExtensionModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactCompletionExtensionModulusTasteGate_round_trip x).symm
      (Eq.trans hread (CompactCompletionExtensionModulusTasteGate_round_trip y)))

instance compactCompletionExtensionModulusBHistCarrier :
    BHistCarrier CompactCompletionExtensionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactCompletionExtensionModulusToEventFlow
  fromEventFlow := compactCompletionExtensionModulusFromEventFlow

instance compactCompletionExtensionModulusChapterTasteGate :
    ChapterTasteGate CompactCompletionExtensionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactCompletionExtensionModulusFromEventFlow
        (compactCompletionExtensionModulusToEventFlow x) = some x
    exact CompactCompletionExtensionModulusTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactCompletionExtensionModulusTasteGate_toEventFlow_injective heq)

theorem CompactCompletionExtensionModulus_modulus_preservation_route
    {Q G B M L R S D E H C P N : BHist}
    (hQGM : Cont Q G M) (hBML : Cont B M L) (hLRS : Cont L R S)
    (hSDE : Cont S D E) (hEHC : Cont E H C) (hCPN : Cont C P N) :
    (∃ route : BHist,
        route = N ∧ Cont Q G M ∧ Cont B M L ∧ Cont L R S ∧ Cont S D E ∧
          Cont E H C ∧ Cont C P route) ∧
      SemanticNameCert
        (fun row : BHist => row = M ∧ Cont Q G M)
        (fun row : BHist => row = M ∨ row = L ∨ row = R ∨ row = S ∨
          row = D ∨ row = E)
        (fun row : BHist => hsame row M ∨ hsame row E ∨ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  constructor
  · exact ⟨N, rfl, hQGM, hBML, hLRS, hSDE, hEHC, hCPN⟩
  · have sourceM :
        (fun row : BHist => row = M ∧ Cont Q G M) M := by
      exact ⟨rfl, hQGM⟩
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
          · exact hQGM
      }
      pattern_sound := by
        intro _row source
        exact Or.inl source.left
      ledger_sound := by
        intro _row source
        exact Or.inl source.left
    }

end BEDC.Derived.CompactCompletionExtensionModulusUp.TasteGate
