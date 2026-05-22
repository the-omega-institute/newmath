import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitUp : Type where
  | mk (S R D A T C H P N : BHist) : LimitUp
  deriving DecidableEq

def limitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitEncodeBHist h

def limitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitDecodeBHist tail)

private theorem LimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limitFields : LimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitUp.mk S R D A T C H P N => [S, R, D, A, T, C, H, P, N]

def limitToEventFlow : LimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (limitFields x).map limitEncodeBHist

def limitFromEventFlow : EventFlow → Option LimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: R :: D :: A :: T :: C :: H :: P :: N :: [] =>
      some
        (LimitUp.mk
          (limitDecodeBHist S)
          (limitDecodeBHist R)
          (limitDecodeBHist D)
          (limitDecodeBHist A)
          (limitDecodeBHist T)
          (limitDecodeBHist C)
          (limitDecodeBHist H)
          (limitDecodeBHist P)
          (limitDecodeBHist N))
  | _ => none

private theorem limit_round_trip :
    ∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D A T C H P N =>
      change
        some
          (LimitUp.mk
            (limitDecodeBHist (limitEncodeBHist S))
            (limitDecodeBHist (limitEncodeBHist R))
            (limitDecodeBHist (limitEncodeBHist D))
            (limitDecodeBHist (limitEncodeBHist A))
            (limitDecodeBHist (limitEncodeBHist T))
            (limitDecodeBHist (limitEncodeBHist C))
            (limitDecodeBHist (limitEncodeBHist H))
            (limitDecodeBHist (limitEncodeBHist P))
            (limitDecodeBHist (limitEncodeBHist N))) =
          some (LimitUp.mk S R D A T C H P N)
      rw [LimitTasteGate_single_carrier_alignment_decode_encode S,
        LimitTasteGate_single_carrier_alignment_decode_encode R,
        LimitTasteGate_single_carrier_alignment_decode_encode D,
        LimitTasteGate_single_carrier_alignment_decode_encode A,
        LimitTasteGate_single_carrier_alignment_decode_encode T,
        LimitTasteGate_single_carrier_alignment_decode_encode C,
        LimitTasteGate_single_carrier_alignment_decode_encode H,
        LimitTasteGate_single_carrier_alignment_decode_encode P,
        LimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem limitToEventFlow_injective {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitFromEventFlow (limitToEventFlow x) =
        limitFromEventFlow (limitToEventFlow y) :=
    congrArg limitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (limit_round_trip x).symm (Eq.trans hread (limit_round_trip y)))

private theorem LimitTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    limitEncodeBHist h = limitEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  calc
    h = limitDecodeBHist (limitEncodeBHist h) :=
      (LimitTasteGate_single_carrier_alignment_decode_encode h).symm
    _ = limitDecodeBHist (limitEncodeBHist k) := congrArg limitDecodeBHist heq
    _ = k := LimitTasteGate_single_carrier_alignment_decode_encode k

private theorem LimitTasteGate_single_carrier_alignment_direct
    {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ R₁ D₁ A₁ T₁ C₁ H₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ D₂ A₂ T₂ C₂ H₂ P₂ N₂ =>
          change
            [limitEncodeBHist S₁, limitEncodeBHist R₁, limitEncodeBHist D₁,
              limitEncodeBHist A₁, limitEncodeBHist T₁, limitEncodeBHist C₁,
              limitEncodeBHist H₁, limitEncodeBHist P₁, limitEncodeBHist N₁] =
              [limitEncodeBHist S₂, limitEncodeBHist R₂, limitEncodeBHist D₂,
                limitEncodeBHist A₂, limitEncodeBHist T₂, limitEncodeBHist C₂,
                limitEncodeBHist H₂, limitEncodeBHist P₂, limitEncodeBHist N₂] at heq
          injection heq with hS tail0
          injection tail0 with hR tail1
          injection tail1 with hD tail2
          injection tail2 with hA tail3
          injection tail3 with hT tail4
          injection tail4 with hC tail5
          injection tail5 with hH tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          have hs := LimitTasteGate_single_carrier_alignment_encode_injective hS
          have hr := LimitTasteGate_single_carrier_alignment_encode_injective hR
          have hd := LimitTasteGate_single_carrier_alignment_encode_injective hD
          have ha := LimitTasteGate_single_carrier_alignment_encode_injective hA
          have ht := LimitTasteGate_single_carrier_alignment_encode_injective hT
          have hc := LimitTasteGate_single_carrier_alignment_encode_injective hC
          have hh := LimitTasteGate_single_carrier_alignment_encode_injective hH
          have hp := LimitTasteGate_single_carrier_alignment_encode_injective hP
          have hn := LimitTasteGate_single_carrier_alignment_encode_injective hN
          subst hs
          subst hr
          subst hd
          subst ha
          subst ht
          subst hc
          subst hh
          subst hp
          subst hn
          rfl

instance limitBHistCarrier : BHistCarrier LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitToEventFlow
  fromEventFlow := limitFromEventFlow

instance limitChapterTasteGate : ChapterTasteGate LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitFromEventFlow (limitToEventFlow x) = some x
    exact limit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limitToEventFlow_injective heq)

theorem LimitTasteGate_single_carrier_alignment (x y : LimitUp) :
    limitToEventFlow x = limitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact LimitTasteGate_single_carrier_alignment_direct

end BEDC.Derived.LimitUp.TasteGate
