import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactEquicontinuousFamilyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactEquicontinuousFamilyModulusUp : Type where
  | mk (X F M U W R S H C P N : BHist) : CompactEquicontinuousFamilyModulusUp
  deriving DecidableEq

def compactEquicontinuousFamilyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactEquicontinuousFamilyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactEquicontinuousFamilyModulusEncodeBHist h

def compactEquicontinuousFamilyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactEquicontinuousFamilyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactEquicontinuousFamilyModulusDecodeBHist tail)

theorem CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactEquicontinuousFamilyModulusToEventFlow :
    CompactEquicontinuousFamilyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactEquicontinuousFamilyModulusUp.mk X F M U W R S H C P N =>
      [compactEquicontinuousFamilyModulusEncodeBHist X,
        compactEquicontinuousFamilyModulusEncodeBHist F,
        compactEquicontinuousFamilyModulusEncodeBHist M,
        compactEquicontinuousFamilyModulusEncodeBHist U,
        compactEquicontinuousFamilyModulusEncodeBHist W,
        compactEquicontinuousFamilyModulusEncodeBHist R,
        compactEquicontinuousFamilyModulusEncodeBHist S,
        compactEquicontinuousFamilyModulusEncodeBHist H,
        compactEquicontinuousFamilyModulusEncodeBHist C,
        compactEquicontinuousFamilyModulusEncodeBHist P,
        compactEquicontinuousFamilyModulusEncodeBHist N]

def compactEquicontinuousFamilyModulusFromEventFlow :
    EventFlow → Option CompactEquicontinuousFamilyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      if h : ef.length = 11 then
        some
          (CompactEquicontinuousFamilyModulusUp.mk
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨0, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨1, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨2, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨3, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨4, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨5, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨6, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨7, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨8, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨9, by rw [h]; decide⟩))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (ef.get ⟨10, by rw [h]; decide⟩)))
      else none

private theorem CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactEquicontinuousFamilyModulusUp,
      compactEquicontinuousFamilyModulusFromEventFlow
        (compactEquicontinuousFamilyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F M U W R S H C P N =>
      change
        (if h :
            [compactEquicontinuousFamilyModulusEncodeBHist X,
              compactEquicontinuousFamilyModulusEncodeBHist F,
              compactEquicontinuousFamilyModulusEncodeBHist M,
              compactEquicontinuousFamilyModulusEncodeBHist U,
              compactEquicontinuousFamilyModulusEncodeBHist W,
              compactEquicontinuousFamilyModulusEncodeBHist R,
              compactEquicontinuousFamilyModulusEncodeBHist S,
              compactEquicontinuousFamilyModulusEncodeBHist H,
              compactEquicontinuousFamilyModulusEncodeBHist C,
              compactEquicontinuousFamilyModulusEncodeBHist P,
              compactEquicontinuousFamilyModulusEncodeBHist N].length = 11 then
            some
              (CompactEquicontinuousFamilyModulusUp.mk
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨0, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨1, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨2, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨3, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨4, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨5, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨6, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨7, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨8, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨9, by rw [h]; decide⟩))
                (compactEquicontinuousFamilyModulusDecodeBHist
                  ([compactEquicontinuousFamilyModulusEncodeBHist X,
                    compactEquicontinuousFamilyModulusEncodeBHist F,
                    compactEquicontinuousFamilyModulusEncodeBHist M,
                    compactEquicontinuousFamilyModulusEncodeBHist U,
                    compactEquicontinuousFamilyModulusEncodeBHist W,
                    compactEquicontinuousFamilyModulusEncodeBHist R,
                    compactEquicontinuousFamilyModulusEncodeBHist S,
                    compactEquicontinuousFamilyModulusEncodeBHist H,
                    compactEquicontinuousFamilyModulusEncodeBHist C,
                    compactEquicontinuousFamilyModulusEncodeBHist P,
                    compactEquicontinuousFamilyModulusEncodeBHist N].get
                    ⟨10, by rw [h]; decide⟩)))
          else none) =
          some (CompactEquicontinuousFamilyModulusUp.mk X F M U W R S H C P N)
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, dite_true, List.get]
      rw [CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode X,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode F,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode M,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode U,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode W,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode R,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode S,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode H,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode C,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode P,
        CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode N]

private theorem
    CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactEquicontinuousFamilyModulusUp} :
    compactEquicontinuousFamilyModulusToEventFlow x =
        compactEquicontinuousFamilyModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk X₁ F₁ M₁ U₁ W₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ F₂ M₂ U₂ W₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          injection heq with hX tailF
          injection tailF with hF tailM
          injection tailM with hM tailU
          injection tailU with hU tailW
          injection tailW with hW tailR
          injection tailR with hR tailS
          injection tailS with hS tailH
          injection tailH with hH tailC
          injection tailC with hC tailP
          injection tailP with hP tailN
          injection tailN with hN _
          have eqX : X₁ = X₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode X₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hX)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode X₂))
          have eqF : F₁ = F₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode F₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hF)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode F₂))
          have eqM : M₁ = M₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode M₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hM)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode M₂))
          have eqU : U₁ = U₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode U₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hU)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode U₂))
          have eqW : W₁ = W₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode W₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hW)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode W₂))
          have eqR : R₁ = R₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode R₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hR)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode R₂))
          have eqS : S₁ = S₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode S₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hS)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode S₂))
          have eqH : H₁ = H₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode H₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hH)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode H₂))
          have eqC : C₁ = C₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode C₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hC)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode C₂))
          have eqP : P₁ = P₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode P₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hP)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode P₂))
          have eqN : N₁ = N₂ :=
            Eq.trans
              (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode N₁).symm
              (Eq.trans (congrArg compactEquicontinuousFamilyModulusDecodeBHist hN)
                (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode N₂))
          subst eqX
          subst eqF
          subst eqM
          subst eqU
          subst eqW
          subst eqR
          subst eqS
          subst eqH
          subst eqC
          subst eqP
          subst eqN
          rfl

instance compactEquicontinuousFamilyModulusBHistCarrier :
    BHistCarrier CompactEquicontinuousFamilyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactEquicontinuousFamilyModulusToEventFlow
  fromEventFlow := compactEquicontinuousFamilyModulusFromEventFlow

instance compactEquicontinuousFamilyModulusChapterTasteGate :
    ChapterTasteGate CompactEquicontinuousFamilyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactEquicontinuousFamilyModulusFromEventFlow
        (compactEquicontinuousFamilyModulusToEventFlow x) = some x
    exact CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactEquicontinuousFamilyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactEquicontinuousFamilyModulusChapterTasteGate

theorem CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEncodeBHist h) = h) ∧
      compactEquicontinuousFamilyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.CompactEquicontinuousFamilyModulusUp
