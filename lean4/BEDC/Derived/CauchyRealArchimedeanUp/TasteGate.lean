import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealArchimedeanUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealArchimedeanUp : Type where
  | mk (G D E W H C P N : BHist) : CauchyRealArchimedeanUp
  deriving DecidableEq

private def cauchyRealArchimedeanEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealArchimedeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealArchimedeanEncodeBHist h

private def cauchyRealArchimedeanDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealArchimedeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealArchimedeanDecodeBHist tail)

private theorem cauchyRealArchimedean_decode_encode_bhist :
    forall h : BHist,
      cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def cauchyRealArchimedeanFields : CauchyRealArchimedeanUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealArchimedeanUp.mk G D E W H C P N => [G, D, E, W, H, C, P, N]

private def cauchyRealArchimedeanToEventFlow : CauchyRealArchimedeanUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | A => (cauchyRealArchimedeanFields A).map cauchyRealArchimedeanEncodeBHist

private def cauchyRealArchimedeanEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealArchimedeanEventAtDefault index rest

private def cauchyRealArchimedeanFromEventFlow
    (ef : EventFlow) : Option CauchyRealArchimedeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealArchimedeanUp.mk
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 0 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 1 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 2 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 3 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 4 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 5 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 6 ef))
      (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEventAtDefault 7 ef)))

private theorem cauchyRealArchimedean_round_trip :
    forall A : CauchyRealArchimedeanUp,
      cauchyRealArchimedeanFromEventFlow (cauchyRealArchimedeanToEventFlow A) =
        some A := by
  -- BEDC touchpoint anchor: BHist BMark
  intro A
  cases A with
  | mk G D E W H C P N =>
      change
        some
          (CauchyRealArchimedeanUp.mk
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist G))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist D))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist E))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist W))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist H))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist C))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist P))
            (cauchyRealArchimedeanDecodeBHist (cauchyRealArchimedeanEncodeBHist N))) =
          some (CauchyRealArchimedeanUp.mk G D E W H C P N)
      rw [cauchyRealArchimedean_decode_encode_bhist G,
        cauchyRealArchimedean_decode_encode_bhist D,
        cauchyRealArchimedean_decode_encode_bhist E,
        cauchyRealArchimedean_decode_encode_bhist W,
        cauchyRealArchimedean_decode_encode_bhist H,
        cauchyRealArchimedean_decode_encode_bhist C,
        cauchyRealArchimedean_decode_encode_bhist P,
        cauchyRealArchimedean_decode_encode_bhist N]

private theorem cauchyRealArchimedeanToEventFlow_injective
    {A B : CauchyRealArchimedeanUp} :
    cauchyRealArchimedeanToEventFlow A = cauchyRealArchimedeanToEventFlow B ->
      A = B := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealArchimedeanFromEventFlow (cauchyRealArchimedeanToEventFlow A) =
        cauchyRealArchimedeanFromEventFlow (cauchyRealArchimedeanToEventFlow B) :=
    congrArg cauchyRealArchimedeanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRealArchimedean_round_trip A).symm
      (Eq.trans hread (cauchyRealArchimedean_round_trip B)))

instance cauchyRealArchimedeanBHistCarrier :
    BHistCarrier CauchyRealArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealArchimedeanToEventFlow
  fromEventFlow := cauchyRealArchimedeanFromEventFlow

instance cauchyRealArchimedeanChapterTasteGate :
    ChapterTasteGate CauchyRealArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro A
    change
      cauchyRealArchimedeanFromEventFlow (cauchyRealArchimedeanToEventFlow A) =
        some A
    exact cauchyRealArchimedean_round_trip A
  layer_separation := by
    intro A B hAB heq
    exact hAB (cauchyRealArchimedeanToEventFlow_injective heq)

def CauchyRealArchimedeanCarrierRows (A : CauchyRealArchimedeanUp) : Prop :=
  match A with
  | CauchyRealArchimedeanUp.mk G D E W H C P N =>
      hsame G G /\ hsame D D /\ hsame E E /\ hsame W W /\
        hsame H H /\ hsame C C /\ hsame P P /\ hsame N N

def CauchyRealArchimedeanRouteUses
    (A : CauchyRealArchimedeanUp) (route : BHist) : Prop :=
  match A with
  | CauchyRealArchimedeanUp.mk G D E W H C P N =>
      hsame route BHist.Empty /\ Cont G route G /\ Cont D route D /\
        hsame E E /\ hsame W W /\ hsame H H /\ hsame C C /\ hsame P P /\ hsame N N

def CauchyRealArchimedeanNameCertSurface (A : CauchyRealArchimedeanUp) : Prop :=
  match A with
  | CauchyRealArchimedeanUp.mk _G _D _E _W _H _C _P N =>
      SemanticNameCert
        (fun row : BHist => hsame row N)
        (fun row : BHist => hsame row N /\ CauchyRealArchimedeanCarrierRows A)
        (fun row : BHist => hsame row N /\ CauchyRealArchimedeanRouteUses A BHist.Empty)
        hsame /\
      Nonempty (ChapterTasteGate CauchyRealArchimedeanUp)

theorem CauchyRealArchimedeanCarrier_namecert_obligations
    {A : CauchyRealArchimedeanUp} :
    CauchyRealArchimedeanCarrierRows A /\
      CauchyRealArchimedeanRouteUses A BHist.Empty /\
      CauchyRealArchimedeanNameCertSurface A := by
  -- BEDC touchpoint anchor: BHist hsame Cont NameCert SemanticNameCert ChapterTasteGate
  cases A with
  | mk G D E W H C P N =>
      constructor
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · constructor
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
                  exact ⟨source, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
                ledger_sound := by
                  intro row source
                  exact
                    ⟨source, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
              }
          · exact Nonempty.intro cauchyRealArchimedeanChapterTasteGate

end BEDC.Derived.CauchyRealArchimedeanUp
