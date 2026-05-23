import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WritingItemAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WritingItemAuditUp : Type where
  | mk :
      (itemKind carrier classifier ledger theoryStatus formalStatus gap claimText transport
        continuation provenance name : BHist) →
      WritingItemAuditUp
  deriving DecidableEq

def writingItemAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: writingItemAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: writingItemAuditEncodeBHist h

def writingItemAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (writingItemAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (writingItemAuditDecodeBHist tail)

private theorem writingItemAudit_decode_encode_bhist :
    ∀ h : BHist, writingItemAuditDecodeBHist (writingItemAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def writingItemAuditFields : WritingItemAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WritingItemAuditUp.mk itemKind carrier classifier ledger theoryStatus formalStatus gap
      claimText transport continuation provenance name =>
      [itemKind, carrier, classifier, ledger, theoryStatus, formalStatus, gap, claimText,
        transport, continuation, provenance, name]

def writingItemAuditToEventFlow : WritingItemAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WritingItemAuditUp.mk itemKind carrier classifier ledger theoryStatus formalStatus gap
      claimText transport continuation provenance name =>
      [[BMark.b0], writingItemAuditEncodeBHist itemKind,
        [BMark.b1, BMark.b0], writingItemAuditEncodeBHist carrier,
        [BMark.b1, BMark.b1, BMark.b0], writingItemAuditEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], writingItemAuditEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist theoryStatus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist formalStatus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        writingItemAuditEncodeBHist claimText,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditEncodeBHist name]

private def writingItemAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => writingItemAuditEventAtDefault index rest

def writingItemAuditFromEventFlow (ef : EventFlow) : Option WritingItemAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WritingItemAuditUp.mk
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 1 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 3 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 5 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 7 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 9 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 11 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 13 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 15 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 17 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 19 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 21 ef))
      (writingItemAuditDecodeBHist (writingItemAuditEventAtDefault 23 ef)))

private theorem writingItemAudit_round_trip :
    ∀ x : WritingItemAuditUp,
      writingItemAuditFromEventFlow (writingItemAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk itemKind carrier classifier ledger theoryStatus formalStatus gap claimText transport
      continuation provenance name =>
      change
        some
          (WritingItemAuditUp.mk
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist itemKind))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist carrier))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist classifier))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist ledger))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist theoryStatus))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist formalStatus))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist gap))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist claimText))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist transport))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist continuation))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist provenance))
            (writingItemAuditDecodeBHist (writingItemAuditEncodeBHist name))) =
          some
            (WritingItemAuditUp.mk itemKind carrier classifier ledger theoryStatus formalStatus
              gap claimText transport continuation provenance name)
      rw [writingItemAudit_decode_encode_bhist itemKind,
        writingItemAudit_decode_encode_bhist carrier,
        writingItemAudit_decode_encode_bhist classifier,
        writingItemAudit_decode_encode_bhist ledger,
        writingItemAudit_decode_encode_bhist theoryStatus,
        writingItemAudit_decode_encode_bhist formalStatus,
        writingItemAudit_decode_encode_bhist gap,
        writingItemAudit_decode_encode_bhist claimText,
        writingItemAudit_decode_encode_bhist transport,
        writingItemAudit_decode_encode_bhist continuation,
        writingItemAudit_decode_encode_bhist provenance,
        writingItemAudit_decode_encode_bhist name]

private theorem writingItemAuditToEventFlow_injective {x y : WritingItemAuditUp} :
    writingItemAuditToEventFlow x = writingItemAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      writingItemAuditFromEventFlow (writingItemAuditToEventFlow x) =
        writingItemAuditFromEventFlow (writingItemAuditToEventFlow y) :=
    congrArg writingItemAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (writingItemAudit_round_trip x).symm
      (Eq.trans hread (writingItemAudit_round_trip y)))

private theorem writingItemAudit_field_faithful :
    ∀ x y : WritingItemAuditUp, writingItemAuditFields x = writingItemAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk itemKind₁ carrier₁ classifier₁ ledger₁ theoryStatus₁ formalStatus₁ gap₁ claimText₁
      transport₁ continuation₁ provenance₁ name₁ =>
      cases y with
      | mk itemKind₂ carrier₂ classifier₂ ledger₂ theoryStatus₂ formalStatus₂ gap₂ claimText₂
          transport₂ continuation₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance writingItemAuditBHistCarrier : BHistCarrier WritingItemAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := writingItemAuditToEventFlow
  fromEventFlow := writingItemAuditFromEventFlow

instance writingItemAuditChapterTasteGate : ChapterTasteGate WritingItemAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change writingItemAuditFromEventFlow (writingItemAuditToEventFlow x) = some x
    exact writingItemAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (writingItemAuditToEventFlow_injective heq)

instance writingItemAuditFieldFaithful : FieldFaithful WritingItemAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := writingItemAuditFields
  field_faithful := writingItemAudit_field_faithful

instance writingItemAuditNontrivial : Nontrivial WritingItemAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WritingItemAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WritingItemAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WritingItemAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  writingItemAuditChapterTasteGate

theorem WritingItemAudit_namecert_obligations [AskSetup] [PackageSetup]
    {K C R L T F G Q H U P _N admitted named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont K C admitted →
      Cont admitted R L →
        Cont T F G →
          Cont Q H U →
            Cont U P named →
              PkgSig bundle named pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row named ∧ Cont U P named ∧
                      PkgSig bundle named pkg)
                    (fun row : BHist =>
                      hsame row named ∧ Cont K C admitted ∧ Cont admitted R L ∧
                        Cont T F G ∧ Cont Q H U ∧ Cont U P named)
                    (fun row : BHist => PkgSig bundle named pkg ∧ hsame row named)
                    hsame ∧
                  Cont K C admitted ∧ Cont admitted R L ∧ Cont T F G ∧ Cont Q H U ∧
                    Cont U P named := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro admittedRoute ledgerRoute transportRoute queryRoute namedRoute pkgNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ Cont U P named ∧ PkgSig bundle named pkg)
          (fun row : BHist =>
            hsame row named ∧ Cont K C admitted ∧ Cont admitted R L ∧ Cont T F G ∧
              Cont Q H U ∧ Cont U P named)
          (fun row : BHist => PkgSig bundle named pkg ∧ hsame row named)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro named ⟨hsame_refl named, namedRoute, pkgNamed⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              sourceRow.right.left,
              sourceRow.right.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.left, admittedRoute, ledgerRoute, transportRoute, queryRoute,
            namedRoute⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨pkgNamed, sourceRow.left⟩
    }
  exact
    ⟨cert, admittedRoute, ledgerRoute, transportRoute, queryRoute, namedRoute⟩

end BEDC.Derived.WritingItemAuditUp
