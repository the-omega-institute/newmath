import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DcpoUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DcpoUp : Type where
  | mk (O I W S M F Q L H C P N : BHist) : DcpoUp
  deriving DecidableEq

def dcpoEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dcpoEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dcpoEncodeBHist h

def dcpoDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dcpoDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dcpoDecodeBHist tail)

private theorem dcpoDecode_encode_bhist :
    ∀ h : BHist, dcpoDecodeBHist (dcpoEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dcpoFields : DcpoUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DcpoUp.mk O I W S M F Q L H C P N => [O, I, W, S, M, F, Q, L, H, C, P, N]

def dcpoToEventFlow : DcpoUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dcpoFields x).map dcpoEncodeBHist

def dcpoFromEventFlow : EventFlow → Option DcpoUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | O :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (DcpoUp.mk
                                                          (dcpoDecodeBHist O)
                                                          (dcpoDecodeBHist I)
                                                          (dcpoDecodeBHist W)
                                                          (dcpoDecodeBHist S)
                                                          (dcpoDecodeBHist M)
                                                          (dcpoDecodeBHist F)
                                                          (dcpoDecodeBHist Q)
                                                          (dcpoDecodeBHist L)
                                                          (dcpoDecodeBHist H)
                                                          (dcpoDecodeBHist C)
                                                          (dcpoDecodeBHist P)
                                                          (dcpoDecodeBHist N))
                                                  | _ :: _ => none

private theorem dcpo_round_trip :
    ∀ x : DcpoUp, dcpoFromEventFlow (dcpoToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O I W S M F Q L H C P N =>
      change
        some
          (DcpoUp.mk
            (dcpoDecodeBHist (dcpoEncodeBHist O))
            (dcpoDecodeBHist (dcpoEncodeBHist I))
            (dcpoDecodeBHist (dcpoEncodeBHist W))
            (dcpoDecodeBHist (dcpoEncodeBHist S))
            (dcpoDecodeBHist (dcpoEncodeBHist M))
            (dcpoDecodeBHist (dcpoEncodeBHist F))
            (dcpoDecodeBHist (dcpoEncodeBHist Q))
            (dcpoDecodeBHist (dcpoEncodeBHist L))
            (dcpoDecodeBHist (dcpoEncodeBHist H))
            (dcpoDecodeBHist (dcpoEncodeBHist C))
            (dcpoDecodeBHist (dcpoEncodeBHist P))
            (dcpoDecodeBHist (dcpoEncodeBHist N))) =
          some (DcpoUp.mk O I W S M F Q L H C P N)
      rw [dcpoDecode_encode_bhist O, dcpoDecode_encode_bhist I,
        dcpoDecode_encode_bhist W, dcpoDecode_encode_bhist S,
        dcpoDecode_encode_bhist M, dcpoDecode_encode_bhist F,
        dcpoDecode_encode_bhist Q, dcpoDecode_encode_bhist L,
        dcpoDecode_encode_bhist H, dcpoDecode_encode_bhist C,
        dcpoDecode_encode_bhist P, dcpoDecode_encode_bhist N]

private theorem dcpoToEventFlow_injective {x y : DcpoUp} :
    dcpoToEventFlow x = dcpoToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dcpoFromEventFlow (dcpoToEventFlow x) =
        dcpoFromEventFlow (dcpoToEventFlow y) :=
    congrArg dcpoFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dcpo_round_trip x).symm (Eq.trans hread (dcpo_round_trip y)))

instance dcpoBHistCarrier : BHistCarrier DcpoUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dcpoToEventFlow
  fromEventFlow := dcpoFromEventFlow

instance dcpoChapterTasteGate : ChapterTasteGate DcpoUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dcpoFromEventFlow (dcpoToEventFlow x) = some x
    exact dcpo_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dcpoToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DcpoUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dcpoChapterTasteGate

theorem DcpoScottDomainCompatibility (x : DcpoUp) :
    ∃ O I W S M F Q L H C P N : BHist,
      x = DcpoUp.mk O I W S M F Q L H C P N ∧
        dcpoFields x = [O, I, W, S, M, F, Q, L, H, C, P, N] ∧
          Cont O I (append O I) ∧
            Cont W S (append W S) ∧
              Cont M F (append M F) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk O I W S M F Q L H C P N =>
      exact ⟨O, I, W, S, M, F, Q, L, H, C, P, N, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.DcpoUp
