import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ResearchProgrammeAuditLoopUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ResearchProgrammeAuditLoopUp : Type where
  | mk (S Q G F K A X J T P N : BHist) : ResearchProgrammeAuditLoopUp
  deriving DecidableEq

def researchProgrammeAuditLoopEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: researchProgrammeAuditLoopEncodeBHist h
  | BHist.e1 h => BMark.b1 :: researchProgrammeAuditLoopEncodeBHist h

def researchProgrammeAuditLoopDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (researchProgrammeAuditLoopDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (researchProgrammeAuditLoopDecodeBHist tail)

private theorem researchProgrammeAuditLoop_decode_encode_bhist :
    ∀ h : BHist,
      researchProgrammeAuditLoopDecodeBHist (researchProgrammeAuditLoopEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem researchProgrammeAuditLoop_mk_congr
    {S S' Q Q' G G' F F' K K' A A' X X' J J' T T' P P' N N' : BHist}
    (hS : S' = S)
    (hQ : Q' = Q)
    (hG : G' = G)
    (hF : F' = F)
    (hK : K' = K)
    (hA : A' = A)
    (hX : X' = X)
    (hJ : J' = J)
    (hT : T' = T)
    (hP : P' = P)
    (hN : N' = N) :
    ResearchProgrammeAuditLoopUp.mk S' Q' G' F' K' A' X' J' T' P' N' =
      ResearchProgrammeAuditLoopUp.mk S Q G F K A X J T P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hQ
  cases hG
  cases hF
  cases hK
  cases hA
  cases hX
  cases hJ
  cases hT
  cases hP
  cases hN
  rfl

def researchProgrammeAuditLoopFields :
    ResearchProgrammeAuditLoopUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ResearchProgrammeAuditLoopUp.mk S Q G F K A X J T P N =>
      [S, Q, G, F, K, A, X, J, T, P, N]

def researchProgrammeAuditLoopToEventFlow :
    ResearchProgrammeAuditLoopUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ResearchProgrammeAuditLoopUp.mk S Q G F K A X J T P N =>
      [researchProgrammeAuditLoopEncodeBHist S,
        researchProgrammeAuditLoopEncodeBHist Q,
        researchProgrammeAuditLoopEncodeBHist G,
        researchProgrammeAuditLoopEncodeBHist F,
        researchProgrammeAuditLoopEncodeBHist K,
        researchProgrammeAuditLoopEncodeBHist A,
        researchProgrammeAuditLoopEncodeBHist X,
        researchProgrammeAuditLoopEncodeBHist J,
        researchProgrammeAuditLoopEncodeBHist T,
        researchProgrammeAuditLoopEncodeBHist P,
        researchProgrammeAuditLoopEncodeBHist N]

private def researchProgrammeAuditLoopEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => researchProgrammeAuditLoopEventAtDefault index rest

def researchProgrammeAuditLoopFromEventFlow
    (ef : EventFlow) : Option ResearchProgrammeAuditLoopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ResearchProgrammeAuditLoopUp.mk
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 0 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 1 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 2 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 3 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 4 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 5 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 6 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 7 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 8 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 9 ef))
      (researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEventAtDefault 10 ef)))

private theorem researchProgrammeAuditLoop_round_trip :
    ∀ x : ResearchProgrammeAuditLoopUp,
      researchProgrammeAuditLoopFromEventFlow
        (researchProgrammeAuditLoopToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q G F K A X J T P N =>
      exact
        congrArg some
          (researchProgrammeAuditLoop_mk_congr
            (researchProgrammeAuditLoop_decode_encode_bhist S)
            (researchProgrammeAuditLoop_decode_encode_bhist Q)
            (researchProgrammeAuditLoop_decode_encode_bhist G)
            (researchProgrammeAuditLoop_decode_encode_bhist F)
            (researchProgrammeAuditLoop_decode_encode_bhist K)
            (researchProgrammeAuditLoop_decode_encode_bhist A)
            (researchProgrammeAuditLoop_decode_encode_bhist X)
            (researchProgrammeAuditLoop_decode_encode_bhist J)
            (researchProgrammeAuditLoop_decode_encode_bhist T)
            (researchProgrammeAuditLoop_decode_encode_bhist P)
            (researchProgrammeAuditLoop_decode_encode_bhist N))

private theorem researchProgrammeAuditLoopToEventFlow_injective
    {x y : ResearchProgrammeAuditLoopUp} :
    researchProgrammeAuditLoopToEventFlow x =
        researchProgrammeAuditLoopToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      researchProgrammeAuditLoopFromEventFlow
          (researchProgrammeAuditLoopToEventFlow x) =
        researchProgrammeAuditLoopFromEventFlow
          (researchProgrammeAuditLoopToEventFlow y) :=
    congrArg researchProgrammeAuditLoopFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (researchProgrammeAuditLoop_round_trip x).symm
      (Eq.trans hread (researchProgrammeAuditLoop_round_trip y)))

private theorem researchProgrammeAuditLoop_fields_faithful :
    ∀ x y : ResearchProgrammeAuditLoopUp,
      researchProgrammeAuditLoopFields x = researchProgrammeAuditLoopFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ G₁ F₁ K₁ A₁ X₁ J₁ T₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ G₂ F₂ K₂ A₂ X₂ J₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance researchProgrammeAuditLoopBHistCarrier :
    BHistCarrier ResearchProgrammeAuditLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := researchProgrammeAuditLoopToEventFlow
  fromEventFlow := researchProgrammeAuditLoopFromEventFlow

instance researchProgrammeAuditLoopChapterTasteGate :
    ChapterTasteGate ResearchProgrammeAuditLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      researchProgrammeAuditLoopFromEventFlow
        (researchProgrammeAuditLoopToEventFlow x) = some x
    exact researchProgrammeAuditLoop_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (researchProgrammeAuditLoopToEventFlow_injective heq)

instance researchProgrammeAuditLoopFieldFaithful :
    FieldFaithful ResearchProgrammeAuditLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := researchProgrammeAuditLoopFields
  field_faithful := researchProgrammeAuditLoop_fields_faithful

instance researchProgrammeAuditLoopNontrivial :
    Nontrivial ResearchProgrammeAuditLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ResearchProgrammeAuditLoopUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ResearchProgrammeAuditLoopUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ResearchProgrammeAuditLoopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  researchProgrammeAuditLoopChapterTasteGate

theorem ResearchProgrammeAuditLoopTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      researchProgrammeAuditLoopDecodeBHist
        (researchProgrammeAuditLoopEncodeBHist h) = h) ∧
      (∀ x : ResearchProgrammeAuditLoopUp,
        researchProgrammeAuditLoopFromEventFlow
          (researchProgrammeAuditLoopToEventFlow x) = some x) ∧
        (∀ x y : ResearchProgrammeAuditLoopUp,
          researchProgrammeAuditLoopToEventFlow x =
              researchProgrammeAuditLoopToEventFlow y →
            x = y) ∧
          researchProgrammeAuditLoopEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact researchProgrammeAuditLoop_decode_encode_bhist
  · constructor
    · exact researchProgrammeAuditLoop_round_trip
    · constructor
      · intro x y heq
        exact researchProgrammeAuditLoopToEventFlow_injective heq
      · rfl

end BEDC.Derived.ResearchProgrammeAuditLoopUp
