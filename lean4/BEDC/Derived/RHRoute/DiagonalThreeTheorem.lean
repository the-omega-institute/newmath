import BEDC.Derived.GoedelIncompletenessUp

namespace BEDC.Derived.RHRoute.DiagonalThreeTheorem

universe u v

def PointSurjective {A : Type u} {Y : Type v} (eval : A -> A -> Y) : Prop :=
  (g : A -> Y) -> ∃ a : A, (x : A) -> eval a x = g x

theorem lawvere_fixed_point
    {A : Type u} {Y : Type v} (eval : A -> A -> Y)
    (surjective : PointSurjective eval) (tau : Y -> Y) :
    ∃ y : Y, y = tau y := by
  let diagonal : A -> Y := fun a => tau (eval a a)
  obtain ⟨a, readsDiagonal⟩ := surjective diagonal
  exact ⟨eval a a, readsDiagonal a⟩

theorem lawvere_fixed_point_symm
    {A : Type u} {Y : Type v} (eval : A -> A -> Y)
    (surjective : PointSurjective eval) (tau : Y -> Y) :
    ∃ y : Y, tau y = y := by
  obtain ⟨y, fixed⟩ := lawvere_fixed_point eval surjective tau
  exact ⟨y, fixed.symm⟩

inductive Bit where
  | zero
  | one

namespace Bit

def flip : Bit -> Bit
  | zero => one
  | one => zero

theorem no_fixed_flip : (b : Bit) -> b = flip b -> False
  | zero, h => by
      cases h
  | one, h => by
      cases h

end Bit

def diagonalBit {A : Type u} (eval : A -> A -> Bit) : A -> Bit :=
  fun a => Bit.flip (eval a a)

theorem cantor_no_point_surjection
    {A : Type u} (eval : A -> A -> Bit) :
    PointSurjective eval -> False := by
  intro surjective
  obtain ⟨b, fixed⟩ := lawvere_fixed_point eval surjective Bit.flip
  exact Bit.no_fixed_flip b fixed

theorem cantor_diagonal_row_missed
    {A : Type u} (eval : A -> A -> Bit) (a : A) :
    eval a a = diagonalBit eval a -> False := by
  intro same
  exact Bit.no_fixed_flip (eval a a) same

structure LawvereSelfApplication (Code : Type u) (Sentence : Type v) where
  eval : Code -> Code -> Sentence
  point_surjective : PointSurjective eval

theorem goedel_diagonal_face
    {Code : Type u} {Sentence : Type v}
    (kit : LawvereSelfApplication Code Sentence)
    (transform : Sentence -> Sentence) :
    ∃ sentence : Sentence, sentence = transform sentence :=
  lawvere_fixed_point kit.eval kit.point_surjective transform

structure SameLayerTruthReader (Code : Type u) where
  truthEval : Code -> Code -> Bit
  readsEveryBitPredicate : PointSurjective truthEval

theorem tarski_same_layer_truth_reader_impossible
    {Code : Type u} (reader : SameLayerTruthReader Code) :
    False :=
  cantor_no_point_surjection reader.truthEval reader.readsEveryBitPredicate

theorem diagonal_three_faces
    {Code : Type u} {Sentence : Type v}
    (kit : LawvereSelfApplication Code Sentence)
    (truthEval : Code -> Code -> Bit)
    (transform : Sentence -> Sentence) :
    (∃ sentence : Sentence, sentence = transform sentence) ∧
      (PointSurjective truthEval -> False) ∧
        ((reader : SameLayerTruthReader Code) -> False) := by
  exact
    ⟨goedel_diagonal_face kit transform,
      cantor_no_point_surjection truthEval,
      fun reader => tarski_same_layer_truth_reader_impossible reader⟩

inductive KernelISA where
  | Gen
  | Enc
  | Norm
  | Decode
  | Length
  | Phase
  | Read
  | Ledger
  | Renorm
  | Complete
  | Reflect
  | Certify

namespace KernelISA

def code : KernelISA -> Nat
  | Gen => 0
  | Enc => 1
  | Norm => 2
  | Decode => 3
  | Length => 4
  | Phase => 5
  | Read => 6
  | Ledger => 7
  | Renorm => 8
  | Complete => 9
  | Reflect => 10
  | Certify => 11

def decode : Nat -> Option KernelISA
  | 0 => some Gen
  | 1 => some Enc
  | 2 => some Norm
  | 3 => some Decode
  | 4 => some Length
  | 5 => some Phase
  | 6 => some Read
  | 7 => some Ledger
  | 8 => some Renorm
  | 9 => some Complete
  | 10 => some Reflect
  | 11 => some Certify
  | _ => none

theorem decode_code : (op : KernelISA) -> decode (code op) = some op
  | Gen => rfl
  | Enc => rfl
  | Norm => rfl
  | Decode => rfl
  | Length => rfl
  | Phase => rfl
  | Read => rfl
  | Ledger => rfl
  | Renorm => rfl
  | Complete => rfl
  | Reflect => rfl
  | Certify => rfl

end KernelISA

structure KernelEvent where
  src : Nat
  op : KernelISA
  arg : Nat
  tag : Nat

structure EventCode where
  src : Nat
  op : Nat
  arg : Nat
  tag : Nat

def encodeEvent (event : KernelEvent) : EventCode :=
  { src := event.src
    op := event.op.code
    arg := event.arg
    tag := event.tag }

def decodeEvent (code : EventCode) : Option KernelEvent :=
  match KernelISA.decode code.op with
  | some op =>
      some
        { src := code.src
          op := op
          arg := code.arg
          tag := code.tag }
  | none => none

theorem decode_encode_event (event : KernelEvent) :
    decodeEvent (encodeEvent event) = some event := by
  cases event with
  | mk src op arg tag =>
      cases op with
      | Gen => rfl
      | Enc => rfl
      | Norm => rfl
      | Decode => rfl
      | Length => rfl
      | Phase => rfl
      | Read => rfl
      | Ledger => rfl
      | Renorm => rfl
      | Complete => rfl
      | Reflect => rfl
      | Certify => rfl

abbrev Program := List KernelEvent
abbrev ProgramCode := List EventCode

def encodeProgram : Program -> ProgramCode
  | [] => []
  | event :: rest => encodeEvent event :: encodeProgram rest

def decodeProgram : ProgramCode -> Option Program
  | [] => some []
  | code :: rest =>
      match decodeEvent code with
      | none => none
      | some event =>
          match decodeProgram rest with
          | none => none
          | some program => some (event :: program)

theorem decode_encode_program : (program : Program) ->
    decodeProgram (encodeProgram program) = some program
  | [] => rfl
  | event :: rest => by
      change
        (match decodeEvent (encodeEvent event) with
          | none => none
          | some decodedEvent =>
              match decodeProgram (encodeProgram rest) with
              | none => none
              | some decodedRest => some (decodedEvent :: decodedRest)) =
          some (event :: rest)
      rw [decode_encode_event event, decode_encode_program rest]

structure KernelDescription where
  events : Program

structure SelfCode where
  programCode : ProgramCode

def kernelSelfCode (kernel : KernelDescription) : SelfCode :=
  { programCode := encodeProgram kernel.events }

theorem kernel_self_code_decodes (kernel : KernelDescription) :
    decodeProgram (kernelSelfCode kernel).programCode = some kernel.events := by
  cases kernel with
  | mk events =>
      exact decode_encode_program events

def instructionOfEvent (event : KernelEvent) : KernelISA :=
  event.op

theorem event_opcode_roundtrip (event : KernelEvent) :
    KernelISA.decode (KernelISA.code (instructionOfEvent event)) =
      some (instructionOfEvent event) :=
  KernelISA.decode_code (instructionOfEvent event)

inductive FiniteKernelConcept where
  | atom : Nat -> FiniteKernelConcept
  | combine : KernelISA -> FiniteKernelConcept -> FiniteKernelConcept -> FiniteKernelConcept

def conceptProgram : FiniteKernelConcept -> Program
  | FiniteKernelConcept.atom tag =>
      [{ src := tag, op := KernelISA.Read, arg := tag, tag := tag }]
  | FiniteKernelConcept.combine op left right =>
      conceptProgram left ++ conceptProgram right ++
        [{ src := 0, op := op, arg := 0, tag := op.code }]

theorem finite_concept_self_code_decodes (concept : FiniteKernelConcept) :
    decodeProgram (encodeProgram (conceptProgram concept)) =
      some (conceptProgram concept) :=
  decode_encode_program (conceptProgram concept)

inductive LedgerStatus where
  | open
  | closed
  | semantic

structure PropertyObject where
  history : Program
  code : ProgramCode
  readout : Nat
  ledger : LedgerStatus
  selfCode : SelfCode
  updateRule : KernelISA
  certificate : Nat

def Ont (concept : FiniteKernelConcept) : PropertyObject :=
  { history := conceptProgram concept
    code := encodeProgram (conceptProgram concept)
    readout := 0
    ledger := LedgerStatus.open
    selfCode := { programCode := encodeProgram (conceptProgram concept) }
    updateRule := KernelISA.Certify
    certificate := 0 }

theorem Ont_self_code_decodes (concept : FiniteKernelConcept) :
    decodeProgram (Ont concept).selfCode.programCode =
      some (Ont concept).history :=
  decode_encode_program (conceptProgram concept)

structure SemanticLedgerEntry where
  layer : Nat
  source : Nat
  detector : Nat
  future : Nat

structure OpenLedgerEntry where
  layer : Nat
  source : Nat
  detector : Nat
  future : Nat
  status : LedgerStatus

def shiftSemantic (entry : SemanticLedgerEntry) : OpenLedgerEntry :=
  { layer := Nat.succ entry.layer
    source := entry.source
    detector := entry.detector
    future := entry.future
    status := LedgerStatus.open }

theorem shift_semantic_status_open (entry : SemanticLedgerEntry) :
    (shiftSemantic entry).status = LedgerStatus.open :=
  rfl

theorem shift_semantic_layer_succ (entry : SemanticLedgerEntry) :
    (shiftSemantic entry).layer = Nat.succ entry.layer :=
  rfl

structure InternalizationTower where
  Object : Nat -> Type u
  audit : (n : Nat) -> Object n -> Prop
  promote : (n : Nat) -> Object n -> Object (Nat.succ n)
  promote_audit :
    (n : Nat) -> (x : Object n) -> audit n x -> audit (Nat.succ n) (promote n x)

theorem tower_promote_audit
    (tower : InternalizationTower.{u}) (n : Nat)
    (x : tower.Object n) (cert : tower.audit n x) :
    tower.audit (Nat.succ n) (tower.promote n x) :=
  tower.promote_audit n x cert

structure PropertyLiftObligation where
  layer : Nat
  propertyCode : ProgramCode
  expectedObjectLayer : Nat

def liftObligationFor (layer : Nat) (concept : FiniteKernelConcept) :
    PropertyLiftObligation :=
  { layer := layer
    propertyCode := encodeProgram (conceptProgram concept)
    expectedObjectLayer := Nat.succ layer }

theorem lift_obligation_targets_next_layer
    (layer : Nat) (concept : FiniteKernelConcept) :
    (liftObligationFor layer concept).expectedObjectLayer = Nat.succ layer :=
  rfl

end BEDC.Derived.RHRoute.DiagonalThreeTheorem
