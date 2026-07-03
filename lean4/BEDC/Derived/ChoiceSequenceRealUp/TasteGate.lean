import BEDC.Derived.ChoiceSequenceRealUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoiceSequenceRealUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoiceSequenceRealUp : Type where
  | mk : (prefixRow stream regular dyadic realSeal transport replay provenance nameCert : BHist) →
      ChoiceSequenceRealUp
  deriving DecidableEq

def choiceSequenceRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choiceSequenceRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choiceSequenceRealEncodeBHist h

def choiceSequenceRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choiceSequenceRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choiceSequenceRealDecodeBHist tail)

private theorem choiceSequenceReal_decode_encode_bhist :
    ∀ h : BHist, choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def choiceSequenceRealFields : ChoiceSequenceRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChoiceSequenceRealUp.mk prefixRow stream regular dyadic realSeal transport replay provenance
      nameCert =>
      [prefixRow, stream, regular, dyadic, realSeal, transport, replay, provenance, nameCert]

def choiceSequenceRealToEventFlow : ChoiceSequenceRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map choiceSequenceRealEncodeBHist (choiceSequenceRealFields x)

def choiceSequenceRealFromEventFlow : EventFlow → Option ChoiceSequenceRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | prefixRow :: rest0 =>
      match rest0 with
      | [] => none
      | stream :: rest1 =>
          match rest1 with
          | [] => none
          | regular :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ChoiceSequenceRealUp.mk
                                              (choiceSequenceRealDecodeBHist prefixRow)
                                              (choiceSequenceRealDecodeBHist stream)
                                              (choiceSequenceRealDecodeBHist regular)
                                              (choiceSequenceRealDecodeBHist dyadic)
                                              (choiceSequenceRealDecodeBHist realSeal)
                                              (choiceSequenceRealDecodeBHist transport)
                                              (choiceSequenceRealDecodeBHist replay)
                                              (choiceSequenceRealDecodeBHist provenance)
                                              (choiceSequenceRealDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem choiceSequenceReal_round_trip :
    ∀ x : ChoiceSequenceRealUp,
      choiceSequenceRealFromEventFlow (choiceSequenceRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk prefixRow stream regular dyadic realSeal transport replay provenance nameCert =>
      change
        some
          (ChoiceSequenceRealUp.mk
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist prefixRow))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist stream))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist regular))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist dyadic))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist realSeal))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist transport))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist replay))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist provenance))
            (choiceSequenceRealDecodeBHist (choiceSequenceRealEncodeBHist nameCert))) =
          some
            (ChoiceSequenceRealUp.mk prefixRow stream regular dyadic realSeal transport replay
              provenance nameCert)
      rw [choiceSequenceReal_decode_encode_bhist prefixRow,
        choiceSequenceReal_decode_encode_bhist stream,
        choiceSequenceReal_decode_encode_bhist regular,
        choiceSequenceReal_decode_encode_bhist dyadic,
        choiceSequenceReal_decode_encode_bhist realSeal,
        choiceSequenceReal_decode_encode_bhist transport,
        choiceSequenceReal_decode_encode_bhist replay,
        choiceSequenceReal_decode_encode_bhist provenance,
        choiceSequenceReal_decode_encode_bhist nameCert]

private theorem choiceSequenceRealToEventFlow_injective {x y : ChoiceSequenceRealUp} :
    choiceSequenceRealToEventFlow x = choiceSequenceRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choiceSequenceRealFromEventFlow (choiceSequenceRealToEventFlow x) =
        choiceSequenceRealFromEventFlow (choiceSequenceRealToEventFlow y) :=
    congrArg choiceSequenceRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (choiceSequenceReal_round_trip x).symm
      (Eq.trans hread (choiceSequenceReal_round_trip y)))

private theorem choiceSequenceReal_field_faithful :
    ∀ x y : ChoiceSequenceRealUp, choiceSequenceRealFields x = choiceSequenceRealFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk prefixRow₁ stream₁ regular₁ dyadic₁ realSeal₁ transport₁ replay₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk prefixRow₂ stream₂ regular₂ dyadic₂ realSeal₂ transport₂ replay₂ provenance₂
          nameCert₂ =>
          cases h
          rfl

instance choiceSequenceRealBHistCarrier : BHistCarrier ChoiceSequenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choiceSequenceRealToEventFlow
  fromEventFlow := choiceSequenceRealFromEventFlow

instance choiceSequenceRealChapterTasteGate : ChapterTasteGate ChoiceSequenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change choiceSequenceRealFromEventFlow (choiceSequenceRealToEventFlow x) = some x
    exact choiceSequenceReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (choiceSequenceRealToEventFlow_injective heq)

instance choiceSequenceRealFieldFaithful : FieldFaithful ChoiceSequenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := choiceSequenceRealFields
  field_faithful := choiceSequenceReal_field_faithful

instance choiceSequenceRealNontrivial : Nontrivial ChoiceSequenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChoiceSequenceRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChoiceSequenceRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ChoiceSequenceRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  choiceSequenceRealChapterTasteGate

theorem ChoiceSequenceRealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {prefixRow stream regular dyadic realSeal transport replay provenance nameCert prefixStream
      streamRegular dyadicSeal namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory prefixRow →
      UnaryHistory stream →
        UnaryHistory regular →
          UnaryHistory dyadic →
            UnaryHistory realSeal →
              UnaryHistory transport →
                UnaryHistory replay →
                  Cont prefixRow stream prefixStream →
                    Cont prefixStream regular streamRegular →
                      Cont dyadic realSeal dyadicSeal →
                        Cont dyadicSeal replay namedRead →
                          PkgSig bundle provenance pkg →
                            hsame namedRead nameCert →
                              choiceSequenceRealFields
                                  (ChoiceSequenceRealUp.mk prefixRow stream regular dyadic
                                    realSeal transport replay provenance nameCert) =
                                [prefixRow, stream, regular, dyadic, realSeal, transport, replay,
                                  provenance, nameCert] ∧
                                SemanticNameCert
                                    (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row prefixRow ∨ hsame row stream ∨
                                        hsame row regular ∨ hsame row dyadic ∨
                                          hsame row realSeal ∨ hsame row prefixStream ∨
                                            hsame row streamRegular ∨ hsame row dyadicSeal ∨
                                              hsame row namedRead ∨ hsame row nameCert)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont prefixRow stream prefixStream ∧
                                        Cont prefixStream regular streamRegular ∧
                                          Cont dyadic realSeal dyadicSeal ∧
                                            Cont dyadicSeal replay namedRead ∧
                                              PkgSig bundle provenance pkg)
                                    hsame ∧
                                  UnaryHistory prefixStream ∧ UnaryHistory streamRegular ∧
                                    UnaryHistory dyadicSeal ∧ UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryPrefix unaryStream unaryRegular unaryDyadic unaryRealSeal _unaryTransport
    unaryReplay prefixStreamRoute streamRegularRoute dyadicSealRoute namedReadRoute
    provenancePkg namedReadName
  have unaryPrefixStream : UnaryHistory prefixStream :=
    unary_cont_closed unaryPrefix unaryStream prefixStreamRoute
  have unaryStreamRegular : UnaryHistory streamRegular :=
    unary_cont_closed unaryPrefixStream unaryRegular streamRegularRoute
  have unaryDyadicSeal : UnaryHistory dyadicSeal :=
    unary_cont_closed unaryDyadic unaryRealSeal dyadicSealRoute
  have unaryNamedRead : UnaryHistory namedRead :=
    unary_cont_closed unaryDyadicSeal unaryReplay namedReadRoute
  have unaryNameCert : UnaryHistory nameCert :=
    unary_transport unaryNamedRead namedReadName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row prefixRow ∨ hsame row stream ∨ hsame row regular ∨ hsame row dyadic ∨
              hsame row realSeal ∨ hsame row prefixStream ∨ hsame row streamRegular ∨
                hsame row dyadicSeal ∨ hsame row namedRead ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont prefixRow stream prefixStream ∧
              Cont prefixStream regular streamRegular ∧ Cont dyadic realSeal dyadicSeal ∧
                Cont dyadicSeal replay namedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameCert ⟨hsame_refl nameCert, unaryNameCert⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixStreamRoute, streamRegularRoute, dyadicSealRoute, namedReadRoute,
          provenancePkg⟩
  }
  exact ⟨rfl, cert, unaryPrefixStream, unaryStreamRegular, unaryDyadicSeal, unaryNameCert⟩

end BEDC.Derived.ChoiceSequenceRealUp
