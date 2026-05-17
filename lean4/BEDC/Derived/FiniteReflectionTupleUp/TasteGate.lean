import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteReflectionTupleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteReflectionTupleUp : Type where
  | mk
      (candidate stability admission compilerWitness tupleImage readback transport routes
        provenance request name : BHist) :
      FiniteReflectionTupleUp
  deriving DecidableEq

def finiteReflectionTupleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteReflectionTupleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteReflectionTupleEncodeBHist h

def finiteReflectionTupleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteReflectionTupleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteReflectionTupleDecodeBHist tail)

private theorem finiteReflectionTuple_decode_encode_bhist :
    ∀ h : BHist, finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteReflectionTupleToEventFlow : FiniteReflectionTupleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteReflectionTupleUp.mk candidate stability admission compilerWitness tupleImage
      readback transport routes provenance request name =>
      [[BMark.b0],
        finiteReflectionTupleEncodeBHist candidate,
        [BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist admission,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist compilerWitness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist tupleImage,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteReflectionTupleEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist request,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteReflectionTupleEncodeBHist name]

def finiteReflectionTupleFromEventFlow : EventFlow → Option FiniteReflectionTupleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | candidate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | stability :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | admission :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | compilerWitness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | tupleImage :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | readback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | request :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (FiniteReflectionTupleUp.mk
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    candidate)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    stability)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    admission)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    compilerWitness)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    tupleImage)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    readback)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    transport)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    routes)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    provenance)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    request)
                                                                                                  (finiteReflectionTupleDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem finiteReflectionTuple_round_trip :
    ∀ x : FiniteReflectionTupleUp,
      finiteReflectionTupleFromEventFlow (finiteReflectionTupleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate stability admission compilerWitness tupleImage readback transport routes
      provenance request name =>
      change
        some
          (FiniteReflectionTupleUp.mk
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist candidate))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist stability))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist admission))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist compilerWitness))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist tupleImage))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist readback))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist transport))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist routes))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist provenance))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist request))
            (finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist name))) =
          some
            (FiniteReflectionTupleUp.mk candidate stability admission compilerWitness tupleImage
              readback transport routes provenance request name)
      rw [finiteReflectionTuple_decode_encode_bhist candidate,
        finiteReflectionTuple_decode_encode_bhist stability,
        finiteReflectionTuple_decode_encode_bhist admission,
        finiteReflectionTuple_decode_encode_bhist compilerWitness,
        finiteReflectionTuple_decode_encode_bhist tupleImage,
        finiteReflectionTuple_decode_encode_bhist readback,
        finiteReflectionTuple_decode_encode_bhist transport,
        finiteReflectionTuple_decode_encode_bhist routes,
        finiteReflectionTuple_decode_encode_bhist provenance,
        finiteReflectionTuple_decode_encode_bhist request,
        finiteReflectionTuple_decode_encode_bhist name]

private theorem finiteReflectionTupleToEventFlow_injective {x y : FiniteReflectionTupleUp} :
    finiteReflectionTupleToEventFlow x = finiteReflectionTupleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteReflectionTupleFromEventFlow (finiteReflectionTupleToEventFlow x) =
        finiteReflectionTupleFromEventFlow (finiteReflectionTupleToEventFlow y) :=
    congrArg finiteReflectionTupleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteReflectionTuple_round_trip x).symm
      (Eq.trans hread (finiteReflectionTuple_round_trip y)))

instance finiteReflectionTupleBHistCarrier : BHistCarrier FiniteReflectionTupleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteReflectionTupleToEventFlow
  fromEventFlow := finiteReflectionTupleFromEventFlow

instance finiteReflectionTupleChapterTasteGate : ChapterTasteGate FiniteReflectionTupleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteReflectionTupleFromEventFlow (finiteReflectionTupleToEventFlow x) = some x
    exact finiteReflectionTuple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteReflectionTupleToEventFlow_injective heq)

instance finiteReflectionTupleFieldFaithful : FieldFaithful FiniteReflectionTupleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteReflectionTupleUp.mk candidate stability admission compilerWitness tupleImage
        readback transport routes provenance request name =>
        [candidate, stability, admission, compilerWitness, tupleImage, readback, transport,
          routes, provenance, request, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk candidate₁ stability₁ admission₁ compilerWitness₁ tupleImage₁ readback₁ transport₁
        routes₁ provenance₁ request₁ name₁ =>
        cases y with
        | mk candidate₂ stability₂ admission₂ compilerWitness₂ tupleImage₂ readback₂ transport₂
            routes₂ provenance₂ request₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance finiteReflectionTupleNontrivial : Nontrivial FiniteReflectionTupleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteReflectionTupleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteReflectionTupleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteReflectionTupleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteReflectionTupleChapterTasteGate

theorem FiniteReflectionTupleTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteReflectionTupleDecodeBHist (finiteReflectionTupleEncodeBHist h) = h) ∧
      (∀ x : FiniteReflectionTupleUp,
        finiteReflectionTupleFromEventFlow (finiteReflectionTupleToEventFlow x) = some x) ∧
        (∀ x y : FiniteReflectionTupleUp,
          finiteReflectionTupleToEventFlow x = finiteReflectionTupleToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful FiniteReflectionTupleUp) ∧
            Nonempty (ChapterTasteGate FiniteReflectionTupleUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteReflectionTuple_decode_encode_bhist
  · constructor
    · exact finiteReflectionTuple_round_trip
    · constructor
      · intro x y heq
        exact finiteReflectionTupleToEventFlow_injective heq
      · constructor
        · exact Nonempty.intro finiteReflectionTupleFieldFaithful
        · exact Nonempty.intro finiteReflectionTupleChapterTasteGate

theorem FiniteReflectionTupleNameCert_obligations
    (x : FiniteReflectionTupleUp) :
    ∃ X S A W I R H C P Q N : BHist,
      x = FiniteReflectionTupleUp.mk X S A W I R H C P Q N ∧
        FieldFaithful.fields x = [X, S, A, W, I, R, H, C, P, Q, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
            hsame H H ∧ Cont C P (append C P) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X S A W I R H C P Q N =>
      exact
        ⟨X, S, A, W, I, R, H, C, P, Q, N, rfl, rfl,
          finiteReflectionTupleChapterTasteGate.round_trip
            (FiniteReflectionTupleUp.mk X S A W I R H C P Q N),
          hsame_refl H, rfl⟩

theorem FiniteReflectionTupleCarrier_bridge_facing_row_totality
    (x : FiniteReflectionTupleUp) :
    ∃ X S A W I R H C P Q N : BHist,
      x = FiniteReflectionTupleUp.mk X S A W I R H C P Q N ∧
        FieldFaithful.fields x = [X, S, A, W, I, R, H, C, P, Q, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
            Cont I R (append I R) ∧
              Cont H C (append H C) ∧
                Cont C P (append C P) ∧
                  Cont Q N (append Q N) ∧
                    (Cont (append I R) (BHist.e0 Q) I → False) := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  cases x with
  | mk X S A W I R H C P Q N =>
      exact
        ⟨X, S, A, W, I, R, H, C, P, Q, N, rfl, rfl,
          finiteReflectionTupleChapterTasteGate.round_trip
            (FiniteReflectionTupleUp.mk X S A W I R H C P Q N),
          rfl, rfl, rfl, rfl,
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := I) (k := append I R) (leftTail := R) (rightTail := Q)).left rfl hbad)⟩

end BEDC.Derived.FiniteReflectionTupleUp
