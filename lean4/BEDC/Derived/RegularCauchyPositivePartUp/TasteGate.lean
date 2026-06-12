import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyPositivePartUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyPositivePartUp : Type where
  | mk (X Z W DX DZ A M R E H C L N : BHist) : RegularCauchyPositivePartUp
  deriving DecidableEq

def regularCauchyPositivePartEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyPositivePartEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyPositivePartEncodeBHist h

def regularCauchyPositivePartDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyPositivePartDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyPositivePartDecodeBHist tail)

private theorem RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyPositivePartFields : RegularCauchyPositivePartUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyPositivePartUp.mk X Z W DX DZ A M R E H C L N =>
      [X, Z, W, DX, DZ, A, M, R, E, H, C, L, N]

def regularCauchyPositivePartToEventFlow :
    RegularCauchyPositivePartUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyPositivePartFields x).map regularCauchyPositivePartEncodeBHist

private def regularCauchyPositivePartEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyPositivePartEventAt index rest

def regularCauchyPositivePartFromEventFlow
    (ef : EventFlow) : Option RegularCauchyPositivePartUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyPositivePartUp.mk
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 0 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 1 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 2 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 3 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 4 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 5 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 6 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 7 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 8 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 9 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 10 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 11 ef))
      (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEventAt 12 ef)))

private theorem RegularCauchyPositivePartTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyPositivePartUp,
      regularCauchyPositivePartFromEventFlow
          (regularCauchyPositivePartToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Z W DX DZ A M R E H C L N =>
      change
        some
          (RegularCauchyPositivePartUp.mk
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist X))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist Z))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist W))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist DX))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist DZ))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist A))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist M))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist R))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist E))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist H))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist C))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist L))
            (regularCauchyPositivePartDecodeBHist (regularCauchyPositivePartEncodeBHist N))) =
          some (RegularCauchyPositivePartUp.mk X Z W DX DZ A M R E H C L N)
      rw [RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode X,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode Z,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode DX,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode DZ,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyPositivePartTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyPositivePartUp} :
    regularCauchyPositivePartToEventFlow x =
        regularCauchyPositivePartToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyPositivePartFromEventFlow
          (regularCauchyPositivePartToEventFlow x) =
        regularCauchyPositivePartFromEventFlow
          (regularCauchyPositivePartToEventFlow y) :=
    congrArg regularCauchyPositivePartFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyPositivePartTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyPositivePartTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyPositivePartTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyPositivePartUp,
      regularCauchyPositivePartFields x = regularCauchyPositivePartFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Z₁ W₁ DX₁ DZ₁ A₁ M₁ R₁ E₁ H₁ C₁ L₁ N₁ =>
      cases y with
      | mk X₂ Z₂ W₂ DX₂ DZ₂ A₂ M₂ R₂ E₂ H₂ C₂ L₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyPositivePartBHistCarrier :
    BHistCarrier RegularCauchyPositivePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyPositivePartToEventFlow
  fromEventFlow := regularCauchyPositivePartFromEventFlow

instance regularCauchyPositivePartChapterTasteGate :
    ChapterTasteGate RegularCauchyPositivePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyPositivePartFromEventFlow
          (regularCauchyPositivePartToEventFlow x) =
        some x
    exact RegularCauchyPositivePartTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyPositivePartTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyPositivePartFieldFaithful :
    FieldFaithful RegularCauchyPositivePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyPositivePartFields
  field_faithful := RegularCauchyPositivePartTasteGate_single_carrier_alignment_fields

instance regularCauchyPositivePartNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyPositivePartUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyPositivePartUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyPositivePartUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyPositivePartUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyPositivePartChapterTasteGate

theorem RegularCauchyPositivePartTasteGate_single_carrier_alignment :
    (∀ x : RegularCauchyPositivePartUp,
      regularCauchyPositivePartFromEventFlow
          (regularCauchyPositivePartToEventFlow x) =
        some x) ∧
      (∀ x y : RegularCauchyPositivePartUp,
        regularCauchyPositivePartToEventFlow x =
            regularCauchyPositivePartToEventFlow y →
          x = y) ∧
        regularCauchyPositivePartFields
            (RegularCauchyPositivePartUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RegularCauchyPositivePartTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyPositivePartTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyPositivePartUp
