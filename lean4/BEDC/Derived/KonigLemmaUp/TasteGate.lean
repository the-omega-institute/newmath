import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KonigLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KonigLemmaUp : Type where
  | mk (T F W Q S A H C P N : BHist) : KonigLemmaUp
  deriving DecidableEq

def konigLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: konigLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: konigLemmaEncodeBHist h

def konigLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (konigLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (konigLemmaDecodeBHist tail)

theorem KonigLemmaTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, konigLemmaDecodeBHist (konigLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def konigLemmaFields : KonigLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KonigLemmaUp.mk T F W Q S A H C P N => [T, F, W, Q, S, A, H, C, P, N]

def konigLemmaToEventFlow : KonigLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (konigLemmaFields x).map konigLemmaEncodeBHist

def konigLemmaFromEventFlow : EventFlow → Option KonigLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | T :: F :: W :: Q :: S :: A :: H :: C :: P :: N :: [] =>
      some
        (KonigLemmaUp.mk
          (konigLemmaDecodeBHist T)
          (konigLemmaDecodeBHist F)
          (konigLemmaDecodeBHist W)
          (konigLemmaDecodeBHist Q)
          (konigLemmaDecodeBHist S)
          (konigLemmaDecodeBHist A)
          (konigLemmaDecodeBHist H)
          (konigLemmaDecodeBHist C)
          (konigLemmaDecodeBHist P)
          (konigLemmaDecodeBHist N))
  | _ => none

private theorem KonigLemmaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KonigLemmaUp,
      konigLemmaFromEventFlow (konigLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T F W Q S A H C P N =>
      change
        some
          (KonigLemmaUp.mk
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist T))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist F))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist W))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist Q))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist S))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist A))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist H))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist C))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist P))
            (konigLemmaDecodeBHist (konigLemmaEncodeBHist N))) =
          some (KonigLemmaUp.mk T F W Q S A H C P N)
      rw [KonigLemmaTasteGate_single_carrier_alignment_decode T,
        KonigLemmaTasteGate_single_carrier_alignment_decode F,
        KonigLemmaTasteGate_single_carrier_alignment_decode W,
        KonigLemmaTasteGate_single_carrier_alignment_decode Q,
        KonigLemmaTasteGate_single_carrier_alignment_decode S,
        KonigLemmaTasteGate_single_carrier_alignment_decode A,
        KonigLemmaTasteGate_single_carrier_alignment_decode H,
        KonigLemmaTasteGate_single_carrier_alignment_decode C,
        KonigLemmaTasteGate_single_carrier_alignment_decode P,
        KonigLemmaTasteGate_single_carrier_alignment_decode N]

private theorem KonigLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KonigLemmaUp} :
    konigLemmaToEventFlow x = konigLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk T1 F1 W1 Q1 S1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 F2 W2 Q2 S2 A2 H2 C2 P2 N2 =>
          change
            [konigLemmaEncodeBHist T1, konigLemmaEncodeBHist F1,
              konigLemmaEncodeBHist W1, konigLemmaEncodeBHist Q1,
              konigLemmaEncodeBHist S1, konigLemmaEncodeBHist A1,
              konigLemmaEncodeBHist H1, konigLemmaEncodeBHist C1,
              konigLemmaEncodeBHist P1, konigLemmaEncodeBHist N1] =
                [konigLemmaEncodeBHist T2, konigLemmaEncodeBHist F2,
                  konigLemmaEncodeBHist W2, konigLemmaEncodeBHist Q2,
                  konigLemmaEncodeBHist S2, konigLemmaEncodeBHist A2,
                  konigLemmaEncodeBHist H2, konigLemmaEncodeBHist C2,
                  konigLemmaEncodeBHist P2, konigLemmaEncodeBHist N2] at heq
          injection heq with hT tail0
          injection tail0 with hF tail1
          injection tail1 with hW tail2
          injection tail2 with hQ tail3
          injection tail3 with hS tail4
          injection tail4 with hA tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          have eT : T1 = T2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode T1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hT)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode T2))
          have eF : F1 = F2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode F1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hF)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode F2))
          have eW : W1 = W2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode W1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hW)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode W2))
          have eQ : Q1 = Q2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode Q1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hQ)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode Q2))
          have eS : S1 = S2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode S1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hS)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode S2))
          have eA : A1 = A2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode A1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hA)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode A2))
          have eH : H1 = H2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode H1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hH)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode H2))
          have eC : C1 = C2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode C1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hC)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode C2))
          have eP : P1 = P2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode P1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hP)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode P2))
          have eN : N1 = N2 := by
            exact
              Eq.trans (KonigLemmaTasteGate_single_carrier_alignment_decode N1).symm
                (Eq.trans (congrArg konigLemmaDecodeBHist hN)
                  (KonigLemmaTasteGate_single_carrier_alignment_decode N2))
          cases eT
          cases eF
          cases eW
          cases eQ
          cases eS
          cases eA
          cases eH
          cases eC
          cases eP
          cases eN
          rfl

private theorem KonigLemmaTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : KonigLemmaUp, konigLemmaFields x = konigLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 F1 W1 Q1 S1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 F2 W2 Q2 S2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance konigLemmaBHistCarrier : BHistCarrier KonigLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := konigLemmaToEventFlow
  fromEventFlow := konigLemmaFromEventFlow

instance konigLemmaChapterTasteGate : ChapterTasteGate KonigLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => by
    change konigLemmaFromEventFlow (konigLemmaToEventFlow x) = some x
    exact KonigLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KonigLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance konigLemmaFieldFaithful : FieldFaithful KonigLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := konigLemmaFields
  field_faithful := KonigLemmaTasteGate_single_carrier_alignment_field_faithful

instance konigLemmaNontrivial : BEDC.Meta.TasteGate.Nontrivial KonigLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KonigLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KonigLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KonigLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  konigLemmaChapterTasteGate

theorem KonigLemmaTasteGate_single_carrier_alignment :
    konigLemmaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  rfl

end BEDC.Derived.KonigLemmaUp
