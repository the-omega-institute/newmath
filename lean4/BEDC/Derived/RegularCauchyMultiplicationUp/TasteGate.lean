import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMultiplicationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMultiplicationUp : Type where
  | mk (X Y W D B E M Z H C P N : BHist) : RegularCauchyMultiplicationUp
  deriving DecidableEq

def regularCauchyMultiplicationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMultiplicationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMultiplicationEncodeBHist h

def regularCauchyMultiplicationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMultiplicationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMultiplicationDecodeBHist tail)

private theorem RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMultiplicationFields : RegularCauchyMultiplicationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N =>
      [X, Y, W, D, B, E, M, Z, H, C, P, N]

def regularCauchyMultiplicationToEventFlow : RegularCauchyMultiplicationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyMultiplicationFields x).map regularCauchyMultiplicationEncodeBHist

private def regularCauchyMultiplicationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMultiplicationEventAtDefault index rest

def regularCauchyMultiplicationFromEventFlow
    (ef : EventFlow) : Option RegularCauchyMultiplicationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMultiplicationUp.mk
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 0 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 1 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 2 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 3 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 4 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 5 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 6 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 7 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 8 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 9 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 10 ef))
      (regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEventAtDefault 11 ef)))

private theorem regularCauchyMultiplication_mk_congr
    {X X' Y Y' W W' D D' B B' E E' M M' Z Z' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hW : W' = W) (hD : D' = D)
    (hB : B' = B) (hE : E' = E) (hM : M' = M) (hZ : Z' = Z)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyMultiplicationUp.mk X' Y' W' D' B' E' M' Z' H' C' P' N' =
      RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hW
  cases hD
  cases hB
  cases hE
  cases hM
  cases hZ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchyMultiplicationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyMultiplicationUp,
      regularCauchyMultiplicationFromEventFlow
        (regularCauchyMultiplicationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D B E M Z H C P N =>
      exact congrArg some
        (regularCauchyMultiplication_mk_congr
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode X)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode Y)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode W)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode D)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode B)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode E)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode M)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode Z)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode H)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode C)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode P)
          (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode N))

private theorem RegularCauchyMultiplicationToEventFlow_injective
    {x y : RegularCauchyMultiplicationUp} :
    regularCauchyMultiplicationToEventFlow x =
      regularCauchyMultiplicationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow x) =
        regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow y) :=
    congrArg regularCauchyMultiplicationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyMultiplicationTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMultiplicationBHistCarrier :
    BHistCarrier RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMultiplicationToEventFlow
  fromEventFlow := regularCauchyMultiplicationFromEventFlow

instance regularCauchyMultiplicationChapterTasteGate :
    ChapterTasteGate RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyMultiplicationFromEventFlow
        (regularCauchyMultiplicationToEventFlow x) = some x
    exact RegularCauchyMultiplicationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMultiplicationToEventFlow_injective heq)

instance regularCauchyMultiplicationFieldFaithful :
    FieldFaithful RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyMultiplicationFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk X₁ Y₁ W₁ D₁ B₁ E₁ M₁ Z₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk X₂ Y₂ W₂ D₂ B₂ E₂ M₂ Z₂ H₂ C₂ P₂ N₂ =>
            injection h with hX rest₁
            injection rest₁ with hY rest₂
            injection rest₂ with hW rest₃
            injection rest₃ with hD rest₄
            injection rest₄ with hB rest₅
            injection rest₅ with hE rest₆
            injection rest₆ with hM rest₇
            injection rest₇ with hZ rest₈
            injection rest₈ with hH rest₉
            injection rest₉ with hC rest₁₀
            injection rest₁₀ with hP rest₁₁
            injection rest₁₁ with hN _
            cases hX
            cases hY
            cases hW
            cases hD
            cases hB
            cases hE
            cases hM
            cases hZ
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance regularCauchyMultiplicationNontrivial :
    Nontrivial RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyMultiplicationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyMultiplicationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hX _ _ _ _ _ _ _ _ _ _ _
        cases hX⟩

def taste_gate : ChapterTasteGate RegularCauchyMultiplicationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMultiplicationChapterTasteGate

theorem RegularCauchyMultiplicationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMultiplicationUp,
        regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyMultiplicationUp,
        regularCauchyMultiplicationToEventFlow x =
          regularCauchyMultiplicationToEventFlow y → x = y) ∧
      regularCauchyMultiplicationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyMultiplicationTasteGate_single_carrier_alignment_decode,
      RegularCauchyMultiplicationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularCauchyMultiplicationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyMultiplicationUp
