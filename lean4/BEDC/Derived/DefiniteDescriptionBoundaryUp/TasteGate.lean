import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DefiniteDescriptionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DefiniteDescriptionBoundaryUp : Type where
  | mk :
      (description existence uniqueness stability transport replay provenance localName : BHist) →
      DefiniteDescriptionBoundaryUp
  deriving DecidableEq

def definiteDescriptionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: definiteDescriptionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: definiteDescriptionBoundaryEncodeBHist h

def definiteDescriptionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (definiteDescriptionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (definiteDescriptionBoundaryDecodeBHist tail)

private theorem definiteDescriptionBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      definiteDescriptionBoundaryDecodeBHist (definiteDescriptionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def definiteDescriptionBoundaryToEventFlow : DefiniteDescriptionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DefiniteDescriptionBoundaryUp.mk description existence uniqueness stability transport replay
      provenance localName =>
      [[BMark.b0],
        definiteDescriptionBoundaryEncodeBHist description,
        [BMark.b1, BMark.b0],
        definiteDescriptionBoundaryEncodeBHist existence,
        [BMark.b1, BMark.b1, BMark.b0],
        definiteDescriptionBoundaryEncodeBHist uniqueness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        definiteDescriptionBoundaryEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        definiteDescriptionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        definiteDescriptionBoundaryEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        definiteDescriptionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        definiteDescriptionBoundaryEncodeBHist localName]

def definiteDescriptionBoundaryFromEventFlow : EventFlow → Option DefiniteDescriptionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | description :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | existence :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | uniqueness :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stability :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DefiniteDescriptionBoundaryUp.mk
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            description)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            existence)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            uniqueness)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            stability)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            transport)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            replay)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            provenance)
                                                                          (definiteDescriptionBoundaryDecodeBHist
                                                                            localName))
                                                                  | _ :: _ => none

private theorem definiteDescriptionBoundary_round_trip :
    ∀ x : DefiniteDescriptionBoundaryUp,
      definiteDescriptionBoundaryFromEventFlow
        (definiteDescriptionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk description existence uniqueness stability transport replay provenance localName =>
      change
        some
          (DefiniteDescriptionBoundaryUp.mk
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist description))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist existence))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist uniqueness))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist stability))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist transport))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist replay))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist provenance))
            (definiteDescriptionBoundaryDecodeBHist
              (definiteDescriptionBoundaryEncodeBHist localName))) =
          some
            (DefiniteDescriptionBoundaryUp.mk description existence uniqueness stability
              transport replay provenance localName)
      rw [definiteDescriptionBoundaryDecode_encode_bhist description,
        definiteDescriptionBoundaryDecode_encode_bhist existence,
        definiteDescriptionBoundaryDecode_encode_bhist uniqueness,
        definiteDescriptionBoundaryDecode_encode_bhist stability,
        definiteDescriptionBoundaryDecode_encode_bhist transport,
        definiteDescriptionBoundaryDecode_encode_bhist replay,
        definiteDescriptionBoundaryDecode_encode_bhist provenance,
        definiteDescriptionBoundaryDecode_encode_bhist localName]

private theorem definiteDescriptionBoundaryToEventFlow_injective
    {x y : DefiniteDescriptionBoundaryUp} :
    definiteDescriptionBoundaryToEventFlow x = definiteDescriptionBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      definiteDescriptionBoundaryFromEventFlow (definiteDescriptionBoundaryToEventFlow x) =
        definiteDescriptionBoundaryFromEventFlow (definiteDescriptionBoundaryToEventFlow y) :=
    congrArg definiteDescriptionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (definiteDescriptionBoundary_round_trip x).symm
      (Eq.trans hread (definiteDescriptionBoundary_round_trip y)))

def definiteDescriptionBoundaryFields : DefiniteDescriptionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DefiniteDescriptionBoundaryUp.mk description existence uniqueness stability transport replay
      provenance localName =>
      [description, existence, uniqueness, stability, transport, replay, provenance, localName]

private theorem definiteDescriptionBoundary_field_faithful :
    ∀ x y : DefiniteDescriptionBoundaryUp,
      definiteDescriptionBoundaryFields x = definiteDescriptionBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk description₁ existence₁ uniqueness₁ stability₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk description₂ existence₂ uniqueness₂ stability₂ transport₂ replay₂ provenance₂
          localName₂ =>
          change
              [description₁, existence₁, uniqueness₁, stability₁, transport₁, replay₁,
                provenance₁, localName₁] =
                [description₂, existence₂, uniqueness₂, stability₂, transport₂, replay₂,
                  provenance₂, localName₂] at h
          injection h with hDescription t1
          injection t1 with hExistence t2
          injection t2 with hUniqueness t3
          injection t3 with hStability t4
          injection t4 with hTransport t5
          injection t5 with hReplay t6
          injection t6 with hProvenance t7
          injection t7 with hLocalName _
          cases hDescription
          cases hExistence
          cases hUniqueness
          cases hStability
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hLocalName
          rfl

instance definiteDescriptionBoundaryBHistCarrier : BHistCarrier DefiniteDescriptionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := definiteDescriptionBoundaryToEventFlow
  fromEventFlow := definiteDescriptionBoundaryFromEventFlow

instance definiteDescriptionBoundaryChapterTasteGate :
    ChapterTasteGate DefiniteDescriptionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      definiteDescriptionBoundaryFromEventFlow
        (definiteDescriptionBoundaryToEventFlow x) = some x
    exact definiteDescriptionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (definiteDescriptionBoundaryToEventFlow_injective heq)

instance definiteDescriptionBoundaryFieldFaithful :
    FieldFaithful DefiniteDescriptionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := definiteDescriptionBoundaryFields
  field_faithful := definiteDescriptionBoundary_field_faithful

instance definiteDescriptionBoundaryNontrivial :
    Nontrivial DefiniteDescriptionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DefiniteDescriptionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DefiniteDescriptionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DefiniteDescriptionBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, definiteDescriptionBoundaryDecodeBHist
      (definiteDescriptionBoundaryEncodeBHist h) = h) ∧
      (∀ x : DefiniteDescriptionBoundaryUp,
        definiteDescriptionBoundaryFromEventFlow
          (definiteDescriptionBoundaryToEventFlow x) = some x) ∧
        (∀ x y : DefiniteDescriptionBoundaryUp,
          definiteDescriptionBoundaryToEventFlow x =
            definiteDescriptionBoundaryToEventFlow y → x = y) ∧
          definiteDescriptionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist,
        definiteDescriptionBoundaryDecodeBHist
          (definiteDescriptionBoundaryEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have hround :
      ∀ x : DefiniteDescriptionBoundaryUp,
        definiteDescriptionBoundaryFromEventFlow
          (definiteDescriptionBoundaryToEventFlow x) = some x := by
    intro x
    cases x with
    | mk description existence uniqueness stability transport replay provenance localName =>
        change
          some
            (DefiniteDescriptionBoundaryUp.mk
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist description))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist existence))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist uniqueness))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist stability))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist transport))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist replay))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist provenance))
              (definiteDescriptionBoundaryDecodeBHist
                (definiteDescriptionBoundaryEncodeBHist localName))) =
            some
              (DefiniteDescriptionBoundaryUp.mk description existence uniqueness stability
                transport replay provenance localName)
        rw [hdecode description, hdecode existence, hdecode uniqueness,
          hdecode stability, hdecode transport, hdecode replay, hdecode provenance,
          hdecode localName]
  have hinj :
      ∀ x y : DefiniteDescriptionBoundaryUp,
        definiteDescriptionBoundaryToEventFlow x =
          definiteDescriptionBoundaryToEventFlow y → x = y := by
    intro x y heq
    have hread :
        definiteDescriptionBoundaryFromEventFlow (definiteDescriptionBoundaryToEventFlow x) =
          definiteDescriptionBoundaryFromEventFlow (definiteDescriptionBoundaryToEventFlow y) :=
      congrArg definiteDescriptionBoundaryFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact ⟨hdecode, hround, hinj, rfl⟩

theorem DefiniteDescriptionBoundaryLedger_exhaustion :
    (∀ x : DefiniteDescriptionBoundaryUp,
      ∃ D E U S H C P N : BHist,
        x = DefiniteDescriptionBoundaryUp.mk D E U S H C P N ∧
          FieldFaithful.fields x = [D, E, U, S, H, C, P, N] ∧
            hsame H H ∧ Cont C P (append C P)) ∧
      (∀ E U S H C P N : BHist,
        FieldFaithful.fields
            (DefiniteDescriptionBoundaryUp.mk (BHist.e0 BHist.Empty) E U S H C P N) ≠
          FieldFaithful.fields
            (DefiniteDescriptionBoundaryUp.mk BHist.Empty E U S H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk D E U S H C P N =>
        exact ⟨D, E, U, S, H, C, P, N, rfl, rfl, hsame_refl H, rfl⟩
  · intro E U S H C P N hfields
    change
      [BHist.e0 BHist.Empty, E, U, S, H, C, P, N] =
        [BHist.Empty, E, U, S, H, C, P, N] at hfields
    injection hfields with hrow _
    cases hrow

theorem DefiniteDescriptionBoundary_namecert_obligations
    {D E U S H C P N witness boundary stable read : BHist} :
    Cont D E witness →
      Cont E U boundary →
        Cont U S stable →
          Cont stable N read →
            SemanticNameCert
              (fun row : BHist =>
                hsame row read ∧
                  ∃ packet : DefiniteDescriptionBoundaryUp,
                    packet = DefiniteDescriptionBoundaryUp.mk D E U S H C P N)
              (fun row : BHist =>
                Cont D E witness ∧ Cont E U boundary ∧ Cont U S stable ∧
                  Cont stable N row)
              (fun row : BHist => hsame row read ∧ hsame H H ∧ hsame C C ∧ hsame P P)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro descriptionWitness existenceBoundary uniquenessStable stableRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro read
          (And.intro (hsame_refl read)
            (Exists.intro (DefiniteDescriptionBoundaryUp.mk D E U S H C P N) rfl))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            source.right
    }
    pattern_sound := by
      intro row source
      have stableRow : Cont stable N row := by
        cases source.left
        exact stableRead
      exact
        ⟨descriptionWitness, existenceBoundary, uniquenessStable, stableRow⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, hsame_refl H, hsame_refl C, hsame_refl P⟩
  }

end BEDC.Derived.DefiniteDescriptionBoundaryUp
