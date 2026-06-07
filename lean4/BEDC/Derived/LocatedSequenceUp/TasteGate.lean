import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSequenceUp : Type where
  | mk (S R D L Q H C P N : BHist) : LocatedSequenceUp
  deriving DecidableEq

def locatedSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSequenceEncodeBHist h

def locatedSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSequenceDecodeBHist tail)

theorem LocatedSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedSequenceDecodeBHist (locatedSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSequenceFields : LocatedSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSequenceUp.mk S R D L Q H C P N => [S, R, D, L, Q, H, C, P, N]

def locatedSequenceToEventFlow : LocatedSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedSequenceFields x).map locatedSequenceEncodeBHist

def locatedSequenceFromEventFlow : EventFlow → Option LocatedSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: R :: D :: L :: Q :: H :: C :: P :: N :: [] =>
      some
        (LocatedSequenceUp.mk
          (locatedSequenceDecodeBHist S)
          (locatedSequenceDecodeBHist R)
          (locatedSequenceDecodeBHist D)
          (locatedSequenceDecodeBHist L)
          (locatedSequenceDecodeBHist Q)
          (locatedSequenceDecodeBHist H)
          (locatedSequenceDecodeBHist C)
          (locatedSequenceDecodeBHist P)
          (locatedSequenceDecodeBHist N))
  | _ => none

private theorem locatedSequence_round_trip :
    ∀ x : LocatedSequenceUp,
      locatedSequenceFromEventFlow (locatedSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D L Q H C P N =>
      change
        some
          (LocatedSequenceUp.mk
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist S))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist R))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
            (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N))) =
          some (LocatedSequenceUp.mk S R D L Q H C P N)
      have eS :
          LocatedSequenceUp.mk
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist S))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist R))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist R))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist R))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode S)
      have eR :
          LocatedSequenceUp.mk S
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist R))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode R)
      have eD :
          LocatedSequenceUp.mk S R
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist D))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S R z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode D)
      have eL :
          LocatedSequenceUp.mk S R D
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist L))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D L
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S R D z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode L)
      have eQ :
          LocatedSequenceUp.mk S R D L
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist Q))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D L Q
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S R D L z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode Q)
      have eH :
          LocatedSequenceUp.mk S R D L Q
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist H))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D L Q H
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S R D L Q z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode H)
      have eC :
          LocatedSequenceUp.mk S R D L Q H
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist C))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D L Q H C
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S R D L Q H z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode C)
      have eP :
          LocatedSequenceUp.mk S R D L Q H C
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist P))
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D L Q H C P
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) :=
        congrArg
          (fun z =>
            LocatedSequenceUp.mk S R D L Q H C z
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)))
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode P)
      have eN :
          LocatedSequenceUp.mk S R D L Q H C P
              (locatedSequenceDecodeBHist (locatedSequenceEncodeBHist N)) =
            LocatedSequenceUp.mk S R D L Q H C P N :=
        congrArg (fun z => LocatedSequenceUp.mk S R D L Q H C P z)
          (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode N)
      exact congrArg some
        (Eq.trans eS
          (Eq.trans eR
            (Eq.trans eD
              (Eq.trans eL
                (Eq.trans eQ
                  (Eq.trans eH
                    (Eq.trans eC (Eq.trans eP eN))))))))

theorem LocatedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedSequenceUp} :
    locatedSequenceToEventFlow x = locatedSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ R₁ D₁ L₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ D₂ L₂ Q₂ H₂ C₂ P₂ N₂ =>
          change
            [locatedSequenceEncodeBHist S₁, locatedSequenceEncodeBHist R₁,
              locatedSequenceEncodeBHist D₁, locatedSequenceEncodeBHist L₁,
              locatedSequenceEncodeBHist Q₁, locatedSequenceEncodeBHist H₁,
              locatedSequenceEncodeBHist C₁, locatedSequenceEncodeBHist P₁,
              locatedSequenceEncodeBHist N₁] =
            [locatedSequenceEncodeBHist S₂, locatedSequenceEncodeBHist R₂,
              locatedSequenceEncodeBHist D₂, locatedSequenceEncodeBHist L₂,
              locatedSequenceEncodeBHist Q₂, locatedSequenceEncodeBHist H₂,
              locatedSequenceEncodeBHist C₂, locatedSequenceEncodeBHist P₂,
              locatedSequenceEncodeBHist N₂] at heq
          injection heq with hS tS
          injection tS with hR tR
          injection tR with hD tD
          injection tD with hL tL
          injection tL with hQ tQ
          injection tQ with hH tH
          injection tH with hC tC
          injection tC with hP tP
          injection tP with hN _
          have sameS : S₁ = S₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode S₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hS)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode S₂))
          have sameR : R₁ = R₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode R₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hR)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode R₂))
          have sameD : D₁ = D₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode D₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hD)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode D₂))
          have sameL : L₁ = L₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode L₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hL)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode L₂))
          have sameQ : Q₁ = Q₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode Q₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hQ)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode Q₂))
          have sameH : H₁ = H₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode H₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hH)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode H₂))
          have sameC : C₁ = C₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode C₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hC)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode C₂))
          have sameP : P₁ = P₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode P₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hP)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode P₂))
          have sameN : N₁ = N₂ :=
            Eq.trans (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode N₁).symm
              (Eq.trans (congrArg locatedSequenceDecodeBHist hN)
                (LocatedSequenceTasteGate_single_carrier_alignment_decode_encode N₂))
          subst sameS
          subst sameR
          subst sameD
          subst sameL
          subst sameQ
          subst sameH
          subst sameC
          subst sameP
          subst sameN
          rfl

instance locatedSequenceBHistCarrier : BHistCarrier LocatedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSequenceToEventFlow
  fromEventFlow := locatedSequenceFromEventFlow

instance locatedSequenceChapterTasteGate : ChapterTasteGate LocatedSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSequenceFromEventFlow (locatedSequenceToEventFlow x) = some x
    exact locatedSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedSequenceChapterTasteGate

theorem LocatedSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedSequenceDecodeBHist (locatedSequenceEncodeBHist h) = h) ∧
      (∀ x y : LocatedSequenceUp,
        locatedSequenceToEventFlow x = locatedSequenceToEventFlow y → x = y) ∧
        locatedSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedSequenceTasteGate_single_carrier_alignment_decode_encode,
      (fun _ _ heq => LocatedSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedSequenceUp.TasteGate
