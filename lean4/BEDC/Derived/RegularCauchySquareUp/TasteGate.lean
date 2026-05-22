import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySquareUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySquareUp : Type where
  | mk (A WL WR DL DR M E R Z H C P N : BHist) : RegularCauchySquareUp
  deriving DecidableEq

def regularCauchySquareEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySquareEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySquareEncodeBHist h

def regularCauchySquareDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySquareDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySquareDecodeBHist tail)

private theorem RegularCauchySquareTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchySquareDecodeBHist
      (regularCauchySquareEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySquareFields : RegularCauchySquareUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySquareUp.mk A WL WR DL DR M E R Z H C P N =>
      [A, WL, WR, DL, DR, M, E, R, Z, H, C, P, N]

def regularCauchySquareToEventFlow : RegularCauchySquareUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySquareFields x).map regularCauchySquareEncodeBHist

private def regularCauchySquareEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySquareEventAtDefault index rest

def regularCauchySquareFromEventFlow
    (ef : EventFlow) : Option RegularCauchySquareUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySquareUp.mk
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 0 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 1 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 2 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 3 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 4 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 5 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 6 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 7 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 8 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 9 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 10 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 11 ef))
      (regularCauchySquareDecodeBHist (regularCauchySquareEventAtDefault 12 ef)))

private theorem regularCauchySquare_mk_congr
    {A A' WL WL' WR WR' DL DL' DR DR' M M' E E' R R' Z Z' H H' C C' P P'
      N N' : BHist}
    (hA : A' = A) (hWL : WL' = WL) (hWR : WR' = WR) (hDL : DL' = DL)
    (hDR : DR' = DR) (hM : M' = M) (hE : E' = E) (hR : R' = R)
    (hZ : Z' = Z) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RegularCauchySquareUp.mk A' WL' WR' DL' DR' M' E' R' Z' H' C' P' N' =
      RegularCauchySquareUp.mk A WL WR DL DR M E R Z H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hWL
  cases hWR
  cases hDL
  cases hDR
  cases hM
  cases hE
  cases hR
  cases hZ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchySquareTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySquareUp,
      regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A WL WR DL DR M E R Z H C P N =>
      exact congrArg some
        (regularCauchySquare_mk_congr
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode A)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode WL)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode WR)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode DL)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode DR)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode M)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode E)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode R)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode Z)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode H)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode C)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode P)
          (RegularCauchySquareTasteGate_single_carrier_alignment_decode N))

private theorem RegularCauchySquareToEventFlow_injective {x y : RegularCauchySquareUp} :
    regularCauchySquareToEventFlow x = regularCauchySquareToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) =
        regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow y) :=
    congrArg regularCauchySquareFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchySquareTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchySquareTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySquareBHistCarrier : BHistCarrier RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySquareToEventFlow
  fromEventFlow := regularCauchySquareFromEventFlow

instance regularCauchySquareChapterTasteGate :
    ChapterTasteGate RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) = some x
    exact RegularCauchySquareTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchySquareToEventFlow_injective heq)

instance regularCauchySquareFieldFaithful :
    FieldFaithful RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySquareFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk A₁ WL₁ WR₁ DL₁ DR₁ M₁ E₁ R₁ Z₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ WL₂ WR₂ DL₂ DR₂ M₂ E₂ R₂ Z₂ H₂ C₂ P₂ N₂ =>
            injection h with hA rest₁
            injection rest₁ with hWL rest₂
            injection rest₂ with hWR rest₃
            injection rest₃ with hDL rest₄
            injection rest₄ with hDR rest₅
            injection rest₅ with hM rest₆
            injection rest₆ with hE rest₇
            injection rest₇ with hR rest₈
            injection rest₈ with hZ rest₉
            injection rest₉ with hH rest₁₀
            injection rest₁₀ with hC rest₁₁
            injection rest₁₁ with hP rest₁₂
            injection rest₁₂ with hN _
            cases hA
            cases hWL
            cases hWR
            cases hDL
            cases hDR
            cases hM
            cases hE
            cases hR
            cases hZ
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance regularCauchySquareNontrivial : Nontrivial RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySquareUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySquareUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hA _ _ _ _ _ _ _ _ _ _ _ _
        cases hA⟩

def taste_gate : ChapterTasteGate RegularCauchySquareUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySquareChapterTasteGate

theorem RegularCauchySquareTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySquareUp,
        regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchySquareUp,
        regularCauchySquareToEventFlow x = regularCauchySquareToEventFlow y → x = y) ∧
      regularCauchySquareEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySquareTasteGate_single_carrier_alignment_decode,
      RegularCauchySquareTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularCauchySquareToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySquareUp
