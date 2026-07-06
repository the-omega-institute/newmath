import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorBranchAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursorBranchAuditUp : Type where
  | mk :
      (inductiveName signature recursor motive branches descent output transport routes
        provenance nameCert : BHist) →
      RecursorBranchAuditUp
  deriving DecidableEq

def recursorBranchAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorBranchAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorBranchAuditEncodeBHist h

def recursorBranchAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorBranchAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorBranchAuditDecodeBHist tail)

private theorem recursorBranchAudit_decode_encode_bhist :
    ∀ h : BHist,
      recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def recursorBranchAuditToEventFlow : RecursorBranchAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchAuditUp.mk inductiveName signature recursor motive branches descent output
      transport routes provenance nameCert =>
      [[BMark.b0],
        recursorBranchAuditEncodeBHist inductiveName,
        [BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist signature,
        [BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist recursor,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist motive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist branches,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorBranchAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchAuditEncodeBHist nameCert]

def recursorBranchAuditFromEventFlow : EventFlow → Option RecursorBranchAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | inductiveName :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | signature :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recursor :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | motive :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | branches :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | descent :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | output :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | nameCert ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RecursorBranchAuditUp.mk
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    inductiveName)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    signature)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    recursor)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    motive)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    branches)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    descent)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    output)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    transport)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    routes)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    provenance)
                                                                                                  (recursorBranchAuditDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem recursorBranchAudit_round_trip :
    ∀ x : RecursorBranchAuditUp,
      recursorBranchAuditFromEventFlow (recursorBranchAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inductiveName signature recursor motive branches descent output transport routes
      provenance nameCert =>
      change
        some
          (RecursorBranchAuditUp.mk
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist inductiveName))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist signature))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist recursor))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist motive))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist branches))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist descent))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist output))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist transport))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist routes))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist provenance))
            (recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist nameCert))) =
          some
            (RecursorBranchAuditUp.mk inductiveName signature recursor motive branches
              descent output transport routes provenance nameCert)
      rw [recursorBranchAudit_decode_encode_bhist inductiveName,
        recursorBranchAudit_decode_encode_bhist signature,
        recursorBranchAudit_decode_encode_bhist recursor,
        recursorBranchAudit_decode_encode_bhist motive,
        recursorBranchAudit_decode_encode_bhist branches,
        recursorBranchAudit_decode_encode_bhist descent,
        recursorBranchAudit_decode_encode_bhist output,
        recursorBranchAudit_decode_encode_bhist transport,
        recursorBranchAudit_decode_encode_bhist routes,
        recursorBranchAudit_decode_encode_bhist provenance,
        recursorBranchAudit_decode_encode_bhist nameCert]

private theorem recursorBranchAuditToEventFlow_injective {x y : RecursorBranchAuditUp} :
    recursorBranchAuditToEventFlow x = recursorBranchAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorBranchAuditFromEventFlow (recursorBranchAuditToEventFlow x) =
        recursorBranchAuditFromEventFlow (recursorBranchAuditToEventFlow y) :=
    congrArg recursorBranchAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorBranchAudit_round_trip x).symm
      (Eq.trans hread (recursorBranchAudit_round_trip y)))

def recursorBranchAuditFields : RecursorBranchAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchAuditUp.mk inductiveName signature recursor motive branches descent output
      transport routes provenance nameCert =>
      [inductiveName, signature, recursor, motive, branches, descent, output, transport,
        routes, provenance, nameCert]

private theorem recursorBranchAudit_field_faithful :
    ∀ x y : RecursorBranchAuditUp,
      recursorBranchAuditFields x = recursorBranchAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk inductiveName signature recursor motive branches descent output transport routes
      provenance nameCert =>
      cases y with
      | mk inductiveName' signature' recursor' motive' branches' descent' output'
          transport' routes' provenance' nameCert' =>
          cases hfields
          rfl

instance recursorBranchAuditBHistCarrier : BHistCarrier RecursorBranchAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursorBranchAuditToEventFlow
  fromEventFlow := recursorBranchAuditFromEventFlow

instance recursorBranchAuditChapterTasteGate : ChapterTasteGate RecursorBranchAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change recursorBranchAuditFromEventFlow (recursorBranchAuditToEventFlow x) = some x
    exact recursorBranchAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursorBranchAuditToEventFlow_injective heq)

instance recursorBranchAuditFieldFaithful : FieldFaithful RecursorBranchAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := recursorBranchAuditFields
  field_faithful := recursorBranchAudit_field_faithful

instance recursorBranchAuditNontrivial : Nontrivial RecursorBranchAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorBranchAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorBranchAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RecursorBranchAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorBranchAuditChapterTasteGate

theorem RecursorBranchAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, recursorBranchAuditDecodeBHist (recursorBranchAuditEncodeBHist h) = h) ∧
      (∀ x : RecursorBranchAuditUp,
        recursorBranchAuditFromEventFlow (recursorBranchAuditToEventFlow x) = some x) ∧
        (∀ x y : RecursorBranchAuditUp,
          recursorBranchAuditToEventFlow x = recursorBranchAuditToEventFlow y → x = y) ∧
          recursorBranchAuditEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RecursorBranchAuditUp,
              recursorBranchAuditFields x = recursorBranchAuditFields y → x = y) ∧
              (∃ x y : RecursorBranchAuditUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact recursorBranchAudit_decode_encode_bhist
  · constructor
    · exact recursorBranchAudit_round_trip
    · constructor
      · intro x y heq
        exact recursorBranchAuditToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact recursorBranchAudit_field_faithful
          · exact
              ⟨RecursorBranchAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                RecursorBranchAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

theorem RecursorBranchAuditCarrier_branch_coverage (x : RecursorBranchAuditUp) :
    exists I S R M B D O H C P N branchReplay : BHist,
      x = RecursorBranchAuditUp.mk I S R M B D O H C P N ∧
        hsame B B ∧
          Cont S B branchReplay ∧ NameCert (fun h : BHist => hsame h B) hsame := by
  -- BEDC touchpoint anchor: BHist BMark Cont NameCert hsame
  cases x with
  | mk I S R M B D O H C P N =>
      refine
        ⟨I, S, R, M, B, D, O, H, C, P, N, append S B, ?_, ?_, ?_, ?_⟩
      · rfl
      · exact hsame_refl B
      · exact cont_intro rfl
      · exact {
          carrier_inhabited := Exists.intro B (hsame_refl B)
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
            exact hsame_trans (hsame_symm sameRows) source
        }

theorem RecursorBranchAuditCarrier_motive_boundary
    {motive branches output : BHist} :
    SemanticNameCert
      (fun row : BHist => hsame row motive ∨ hsame row branches ∨ hsame row output)
      (fun row : BHist => hsame row motive ∨ hsame row branches ∨ hsame row output)
      (fun row : BHist => hsame row motive ∨ hsame row branches ∨ hsame row output)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame
  have sourceMotive :
      (fun row : BHist => hsame row motive ∨ hsame row branches ∨ hsame row output)
        motive := by
    exact Or.inl (hsame_refl motive)
  exact {
    core := {
      carrier_inhabited := Exists.intro motive sourceMotive
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _col same
        exact hsame_symm same
      equiv_trans := by
        intro _row _mid _col sameRowMid sameMidCol
        exact hsame_trans sameRowMid sameMidCol
      carrier_respects_equiv := by
        intro row col same source
        cases source with
        | inl rowMotive =>
            exact Or.inl (hsame_trans (hsame_symm same) rowMotive)
        | inr rest =>
            cases rest with
            | inl rowBranches =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowBranches))
            | inr rowOutput =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm same) rowOutput))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem RecursorBranchAuditCarrier_generator_nonescape (x : RecursorBranchAuditUp) :
    exists I S R M B D O H C P N branchReplay outputReplay : BHist,
      x = RecursorBranchAuditUp.mk I S R M B D O H C P N ∧
        Cont S B branchReplay ∧ Cont branchReplay D outputReplay ∧
          hsame outputReplay (append branchReplay D) ∧
            recursorBranchAuditFromEventFlow (recursorBranchAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame RecursorBranchAuditUp
  cases x with
  | mk I S R M B D O H C P N =>
      refine ⟨I, S, R, M, B, D, O, H, C, P, N, append S B, append (append S B) D, ?_⟩
      constructor
      · rfl
      · constructor
        · exact cont_intro rfl
        · constructor
          · exact cont_intro rfl
          · constructor
            · exact hsame_refl (append (append S B) D)
            · exact
                recursorBranchAudit_round_trip
                  (RecursorBranchAuditUp.mk I S R M B D O H C P N)

end BEDC.Derived.RecursorBranchAuditUp
