import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSequenceLimitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSequenceLimitUp : Type where
  | mk (S W R E H C P N : BHist) : LocatedSequenceLimitUp
  deriving DecidableEq

def locatedSequenceLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSequenceLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSequenceLimitEncodeBHist h

def locatedSequenceLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSequenceLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSequenceLimitDecodeBHist tail)

theorem LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSequenceLimitFields : LocatedSequenceLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSequenceLimitUp.mk S W R E H C P N => [S, W, R, E, H, C, P, N]

def locatedSequenceLimitToEventFlow : LocatedSequenceLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedSequenceLimitFields x).map locatedSequenceLimitEncodeBHist

def locatedSequenceLimitFromEventFlow : EventFlow → Option LocatedSequenceLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: W :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (LocatedSequenceLimitUp.mk
          (locatedSequenceLimitDecodeBHist S)
          (locatedSequenceLimitDecodeBHist W)
          (locatedSequenceLimitDecodeBHist R)
          (locatedSequenceLimitDecodeBHist E)
          (locatedSequenceLimitDecodeBHist H)
          (locatedSequenceLimitDecodeBHist C)
          (locatedSequenceLimitDecodeBHist P)
          (locatedSequenceLimitDecodeBHist N))
  | _ => none

private theorem locatedSequenceLimit_round_trip :
    ∀ x : LocatedSequenceLimitUp,
      locatedSequenceLimitFromEventFlow (locatedSequenceLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W R E H C P N =>
      change
        some
          (LocatedSequenceLimitUp.mk
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist S))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist W))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
            (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N))) =
          some (LocatedSequenceLimitUp.mk S W R E H C P N)
      have eS :
          LocatedSequenceLimitUp.mk
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist S))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist W))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist W))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist W))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode S)
      have eW :
          LocatedSequenceLimitUp.mk S
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist W))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk S z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode W)
      have eR :
          LocatedSequenceLimitUp.mk S W
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist R))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W R
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk S W z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode R)
      have eE :
          LocatedSequenceLimitUp.mk S W R
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist E))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W R E
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk S W R z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode E)
      have eH :
          LocatedSequenceLimitUp.mk S W R E
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist H))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W R E H
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk S W R E z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode H)
      have eC :
          LocatedSequenceLimitUp.mk S W R E H
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist C))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W R E H C
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk S W R E H z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode C)
      have eP :
          LocatedSequenceLimitUp.mk S W R E H C
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist P))
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W R E H C P
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceLimitUp.mk S W R E H C z
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)))
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode P)
      have eN :
          LocatedSequenceLimitUp.mk S W R E H C P
              (locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist N)) =
            LocatedSequenceLimitUp.mk S W R E H C P N :=
        congrArg (fun z => LocatedSequenceLimitUp.mk S W R E H C P z)
          (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode N)
      exact congrArg some
        (Eq.trans eS
          (Eq.trans eW
            (Eq.trans eR
              (Eq.trans eE
                (Eq.trans eH
                  (Eq.trans eC (Eq.trans eP eN)))))))

theorem LocatedSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedSequenceLimitUp} :
    locatedSequenceLimitToEventFlow x = locatedSequenceLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          change
            [locatedSequenceLimitEncodeBHist S₁, locatedSequenceLimitEncodeBHist W₁,
              locatedSequenceLimitEncodeBHist R₁, locatedSequenceLimitEncodeBHist E₁,
              locatedSequenceLimitEncodeBHist H₁, locatedSequenceLimitEncodeBHist C₁,
              locatedSequenceLimitEncodeBHist P₁, locatedSequenceLimitEncodeBHist N₁] =
            [locatedSequenceLimitEncodeBHist S₂, locatedSequenceLimitEncodeBHist W₂,
              locatedSequenceLimitEncodeBHist R₂, locatedSequenceLimitEncodeBHist E₂,
              locatedSequenceLimitEncodeBHist H₂, locatedSequenceLimitEncodeBHist C₂,
              locatedSequenceLimitEncodeBHist P₂, locatedSequenceLimitEncodeBHist N₂] at heq
          injection heq with hS tS
          injection tS with hW tW
          injection tW with hR tR
          injection tR with hE tE
          injection tE with hH tH
          injection tH with hC tC
          injection tC with hP tP
          injection tP with hN _
          have sameS : S₁ = S₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode S₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hS)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode S₂))
          have sameW : W₁ = W₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode W₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hW)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode W₂))
          have sameR : R₁ = R₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode R₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hR)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode R₂))
          have sameE : E₁ = E₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode E₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hE)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode E₂))
          have sameH : H₁ = H₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode H₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hH)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode H₂))
          have sameC : C₁ = C₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode C₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hC)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode C₂))
          have sameP : P₁ = P₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode P₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hP)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode P₂))
          have sameN : N₁ = N₂ :=
            Eq.trans (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode N₁).symm
              (Eq.trans (congrArg locatedSequenceLimitDecodeBHist hN)
                (LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode N₂))
          subst sameS
          subst sameW
          subst sameR
          subst sameE
          subst sameH
          subst sameC
          subst sameP
          subst sameN
          rfl

instance locatedSequenceLimitBHistCarrier : BHistCarrier LocatedSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSequenceLimitToEventFlow
  fromEventFlow := locatedSequenceLimitFromEventFlow

instance locatedSequenceLimitChapterTasteGate : ChapterTasteGate LocatedSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSequenceLimitFromEventFlow (locatedSequenceLimitToEventFlow x) = some x
    exact locatedSequenceLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedSequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedSequenceLimitChapterTasteGate

theorem LocatedSequenceLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedSequenceLimitDecodeBHist (locatedSequenceLimitEncodeBHist h) = h) ∧
      (∀ x y : LocatedSequenceLimitUp,
        locatedSequenceLimitToEventFlow x = locatedSequenceLimitToEventFlow y → x = y) ∧
        locatedSequenceLimitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedSequenceLimitTasteGate_single_carrier_alignment_decode_encode,
      (fun _ _ heq =>
        LocatedSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedSequenceLimitUp.TasteGate
