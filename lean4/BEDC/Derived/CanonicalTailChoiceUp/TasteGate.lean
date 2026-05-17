import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CanonicalTailChoiceUp : Type where
  | mk : (M E I T S R H C0 P N : BHist) → CanonicalTailChoiceUp
  deriving DecidableEq

def canonicalTailChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: canonicalTailChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: canonicalTailChoiceEncodeBHist h

def canonicalTailChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (canonicalTailChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (canonicalTailChoiceDecodeBHist tail)

private theorem canonicalTailChoiceDecode_encode_bhist :
    ∀ h : BHist,
      canonicalTailChoiceDecodeBHist (canonicalTailChoiceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def canonicalTailChoiceToEventFlow : CanonicalTailChoiceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CanonicalTailChoiceUp.mk M E I T S R H C0 P N =>
      [[BMark.b1, BMark.b0, BMark.b0, BMark.b1],
        canonicalTailChoiceEncodeBHist M,
        canonicalTailChoiceEncodeBHist E,
        canonicalTailChoiceEncodeBHist I,
        canonicalTailChoiceEncodeBHist T,
        canonicalTailChoiceEncodeBHist S,
        canonicalTailChoiceEncodeBHist R,
        canonicalTailChoiceEncodeBHist H,
        canonicalTailChoiceEncodeBHist C0,
        canonicalTailChoiceEncodeBHist P,
        canonicalTailChoiceEncodeBHist N]

def canonicalTailChoiceFromEventFlow : EventFlow → Option CanonicalTailChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | _tag :: M :: E :: I :: T :: S :: R :: H :: C0 :: P :: N :: [] =>
      some
        (CanonicalTailChoiceUp.mk
          (canonicalTailChoiceDecodeBHist M)
          (canonicalTailChoiceDecodeBHist E)
          (canonicalTailChoiceDecodeBHist I)
          (canonicalTailChoiceDecodeBHist T)
          (canonicalTailChoiceDecodeBHist S)
          (canonicalTailChoiceDecodeBHist R)
          (canonicalTailChoiceDecodeBHist H)
          (canonicalTailChoiceDecodeBHist C0)
          (canonicalTailChoiceDecodeBHist P)
          (canonicalTailChoiceDecodeBHist N))
  | _ => none

def canonicalTailChoiceFields : CanonicalTailChoiceUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CanonicalTailChoiceUp.mk M E I T S R H C0 P N =>
      [M, E, I, T, S, R, H, C0, P, N]

private theorem canonicalTailChoice_round_trip :
    ∀ x : CanonicalTailChoiceUp,
      canonicalTailChoiceFromEventFlow (canonicalTailChoiceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E I T S R H C0 P N =>
      simp only [canonicalTailChoiceToEventFlow, canonicalTailChoiceFromEventFlow,
        canonicalTailChoiceDecode_encode_bhist]

private theorem canonicalTailChoiceToEventFlow_injective {x y : CanonicalTailChoiceUp} :
    canonicalTailChoiceToEventFlow x = canonicalTailChoiceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = canonicalTailChoiceFromEventFlow (canonicalTailChoiceToEventFlow x) :=
        (canonicalTailChoice_round_trip x).symm
      _ = canonicalTailChoiceFromEventFlow (canonicalTailChoiceToEventFlow y) :=
        congrArg canonicalTailChoiceFromEventFlow hxy
      _ = some y := canonicalTailChoice_round_trip y
  exact Option.some.inj optionEq

instance canonicalTailChoiceBHistCarrier : BHistCarrier CanonicalTailChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := canonicalTailChoiceToEventFlow
  fromEventFlow := canonicalTailChoiceFromEventFlow

instance canonicalTailChoiceChapterTasteGate : ChapterTasteGate CanonicalTailChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change canonicalTailChoiceFromEventFlow (canonicalTailChoiceToEventFlow x) = some x
    exact canonicalTailChoice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (canonicalTailChoiceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CanonicalTailChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  canonicalTailChoiceChapterTasteGate

instance canonicalTailChoiceFieldFaithful : FieldFaithful CanonicalTailChoiceUp where
  fields := canonicalTailChoiceFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk M1 E1 I1 T1 S1 R1 H1 C01 P1 N1 =>
        cases y with
        | mk M2 E2 I2 T2 S2 R2 H2 C02 P2 N2 =>
            injection h with hM t1
            injection t1 with hE t2
            injection t2 with hI t3
            injection t3 with hT t4
            injection t4 with hS t5
            injection t5 with hR t6
            injection t6 with hH t7
            injection t7 with hC0 t8
            injection t8 with hP t9
            injection t9 with hN _
            cases hM
            cases hE
            cases hI
            cases hT
            cases hS
            cases hR
            cases hH
            cases hC0
            cases hP
            cases hN
            rfl

instance canonicalTailChoiceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CanonicalTailChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CanonicalTailChoiceUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CanonicalTailChoiceUp.mk
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

end BEDC.Derived.CanonicalTailChoiceUp
