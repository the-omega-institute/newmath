import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SuccessiveApproximationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SuccessiveApproximationUp : Type where
  | mk (I D T W Q L H C P N : BHist) : SuccessiveApproximationUp
  deriving DecidableEq

private def successiveApproximationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: successiveApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: successiveApproximationEncodeBHist h

private def successiveApproximationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (successiveApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (successiveApproximationDecodeBHist tail)

private theorem successiveApproximation_decode_encode_bhist :
    forall h : BHist,
      successiveApproximationDecodeBHist (successiveApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def successiveApproximationFields : SuccessiveApproximationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SuccessiveApproximationUp.mk I D T W Q L H C P N => [I, D, T, W, Q, L, H, C, P, N]

private def successiveApproximationToEventFlow : SuccessiveApproximationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | K => (successiveApproximationFields K).map successiveApproximationEncodeBHist

private def successiveApproximationEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => successiveApproximationEventAtDefault index rest

private def successiveApproximationFromEventFlow
    (ef : EventFlow) : Option SuccessiveApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SuccessiveApproximationUp.mk
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 0 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 1 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 2 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 3 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 4 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 5 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 6 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 7 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 8 ef))
      (successiveApproximationDecodeBHist (successiveApproximationEventAtDefault 9 ef)))

private theorem successiveApproximation_round_trip :
    forall K : SuccessiveApproximationUp,
      successiveApproximationFromEventFlow (successiveApproximationToEventFlow K) =
        some K := by
  -- BEDC touchpoint anchor: BHist BMark
  intro K
  cases K with
  | mk I D T W Q L H C P N =>
      change
        some
          (SuccessiveApproximationUp.mk
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist I))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist D))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist T))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist W))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist Q))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist L))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist H))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist C))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist P))
            (successiveApproximationDecodeBHist (successiveApproximationEncodeBHist N))) =
          some (SuccessiveApproximationUp.mk I D T W Q L H C P N)
      rw [successiveApproximation_decode_encode_bhist I,
        successiveApproximation_decode_encode_bhist D,
        successiveApproximation_decode_encode_bhist T,
        successiveApproximation_decode_encode_bhist W,
        successiveApproximation_decode_encode_bhist Q,
        successiveApproximation_decode_encode_bhist L,
        successiveApproximation_decode_encode_bhist H,
        successiveApproximation_decode_encode_bhist C,
        successiveApproximation_decode_encode_bhist P,
        successiveApproximation_decode_encode_bhist N]

private theorem successiveApproximationToEventFlow_injective
    {K L : SuccessiveApproximationUp} :
    successiveApproximationToEventFlow K = successiveApproximationToEventFlow L ->
      K = L := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      successiveApproximationFromEventFlow (successiveApproximationToEventFlow K) =
        successiveApproximationFromEventFlow (successiveApproximationToEventFlow L) :=
    congrArg successiveApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (successiveApproximation_round_trip K).symm
      (Eq.trans hread (successiveApproximation_round_trip L)))

instance successiveApproximationBHistCarrier :
    BHistCarrier SuccessiveApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := successiveApproximationToEventFlow
  fromEventFlow := successiveApproximationFromEventFlow

instance successiveApproximationChapterTasteGate :
    ChapterTasteGate SuccessiveApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro K
    change
      successiveApproximationFromEventFlow (successiveApproximationToEventFlow K) =
        some K
    exact successiveApproximation_round_trip K
  layer_separation := by
    intro K L hKL heq
    exact hKL (successiveApproximationToEventFlow_injective heq)

def SuccessiveApproximationCarrierRows (K : SuccessiveApproximationUp) : Prop :=
  match K with
  | SuccessiveApproximationUp.mk I D T W Q L H C P N =>
      hsame I I /\ hsame D D /\ hsame T T /\ hsame W W /\ hsame Q Q /\
        hsame L L /\ hsame H H /\ hsame C C /\ hsame P P /\ hsame N N

def SuccessiveApproximationBudgetRouteUses
    (K : SuccessiveApproximationUp) (route : BHist) : Prop :=
  match K with
  | SuccessiveApproximationUp.mk I D T W Q L H C P N =>
      hsame route BHist.Empty /\ Cont I route I /\ Cont D route D /\
        Cont T route T /\ Cont W route W /\ hsame Q Q /\ hsame L L /\
          hsame H H /\ hsame C C /\ hsame P P /\ hsame N N

def SuccessiveApproximationNameCertSurface (K : SuccessiveApproximationUp) : Prop :=
  match K with
  | SuccessiveApproximationUp.mk _I _D _T _W _Q _L _H _C _P N =>
      SemanticNameCert
        (fun row : BHist => hsame row N)
        (fun row : BHist => hsame row N /\ SuccessiveApproximationCarrierRows K)
        (fun row : BHist => hsame row N /\
          SuccessiveApproximationBudgetRouteUses K BHist.Empty)
        hsame /\
      Nonempty (ChapterTasteGate SuccessiveApproximationUp)

theorem SuccessiveApproximationCarrier_namecert_obligations
    {K : SuccessiveApproximationUp} :
    SuccessiveApproximationCarrierRows K /\
      SuccessiveApproximationBudgetRouteUses K BHist.Empty /\
      SuccessiveApproximationNameCertSurface K := by
  -- BEDC touchpoint anchor: BHist hsame Cont NameCert SemanticNameCert ChapterTasteGate
  cases K with
  | mk I D T W Q L H C P N =>
      constructor
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · constructor
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · constructor
          · exact
              { core := {
                  carrier_inhabited := Exists.intro N rfl
                  equiv_refl := by
                    intro row _source
                    exact hsame_refl row
                  equiv_symm := by
                    intro row row' same
                    exact hsame_symm same
                  equiv_trans := by
                    intro row row' row'' sameLeft sameRight
                    exact hsame_trans sameLeft sameRight
                  carrier_respects_equiv := by
                    intro row row' same source
                    exact hsame_trans (hsame_symm same) source
                }
                pattern_sound := by
                  intro row source
                  exact
                    ⟨source, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
                ledger_sound := by
                  intro row source
                  exact
                    ⟨source,
                      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
              }
          · exact Nonempty.intro successiveApproximationChapterTasteGate

end BEDC.Derived.SuccessiveApproximationUp
