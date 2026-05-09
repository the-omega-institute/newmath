import BEDC.GroundCompiler.MotifReportCounts

namespace BEDC.GroundCompiler.MotifReportPrototype

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.SemanticMotif
open BEDC.GroundCompiler.MotifReportCounts

def P3CarryCount
    (S : EventFlow) (recognized : Option (List MotifProfileItem)) :
    MotifCountStatus :=
  MotifCountP3 S CarryRole recognized

def P3SealCount
    (S : EventFlow) (recognized : Option (List MotifProfileItem)) :
    MotifCountStatus :=
  MotifCountP3 S SealRole recognized

def SoundMotifReport
    (Rfam : GeneratedMotifRecognizer -> Prop) (S : EventFlow)
    (candidates : List EventFlow) (recognized : List MotifProfileItem) :
    Prop :=
  CandidateMotifSection S candidates /\
    RecognizedMotifSection Rfam S recognized

theorem candidate_recognized_sections_separate
    {Rfam : GeneratedMotifRecognizer -> Prop} {S : EventFlow}
    {candidates : List EventFlow} {recognized : List MotifProfileItem}
    {M mu L : EventFlow} :
    CandidateMotifSection S candidates ->
      RecognizedMotifSection Rfam S recognized ->
        List.Mem M candidates ->
          Not (MotifProfile Rfam S mu M L) ->
            Not (List.Mem (mu, M, L) recognized) := by
  intro _ hRecognized _ hMissing hMem
  exact hMissing (hRecognized (mu, M, L) hMem)

theorem sound_motif_report_has_recognizer_ledger
    {Rfam : GeneratedMotifRecognizer -> Prop} {S : EventFlow}
    {recognized : List MotifProfileItem} {item : MotifProfileItem} :
    RecognizedMotifSection Rfam S recognized ->
      List.Mem item recognized ->
        exists R : GeneratedMotifRecognizer,
          Rfam R /\ RecognizesMotif R S item.2.1 item.1 /\
            MotifLedger R S item.2.1 item.1 item.2.2 := by
  intro hSound hMem
  exact motif_report_soundness hSound hMem

theorem motif_report_does_not_license_objects :
    exists Rfam : GeneratedMotifRecognizer -> Prop,
      exists S : EventFlow,
        exists candidates : List EventFlow,
          exists recognized : List MotifProfileItem,
            SoundMotifReport Rfam S candidates recognized /\
              Not (AcceptedObjectFlow S) := by
  refine ⟨EmptyRfam, [], [], [], ?_, empty_not_accepted_object_flow⟩
  constructor
  · intro M hMem
    cases hMem
  · intro item hMem
    cases hMem

def DimensionLiftCertificateFlow : EventFlow :=
  [[BMark.b1, BMark.b1]]

def CompletionCertificateFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1]]

def DimensionLiftStructure (S : EventFlow) : Prop :=
  Subflow DimensionLiftCertificateFlow S

def CompletionStructure (S : EventFlow) : Prop :=
  Subflow CompletionCertificateFlow S

def CarryMotifWitnessFlow : EventFlow :=
  [[BMark.b0], [BMark.b1], [BMark.b0, BMark.b1]]

def SealMotifWitnessFlow : EventFlow :=
  [[BMark.b0], [BMark.b0, BMark.b1], [BMark.b1]]

theorem dimension_lift_certificate_absent_from_carry_witness :
    Not (DimensionLiftStructure CarryMotifWitnessFlow) := by
  intro hSub
  have hMem : List.Mem [BMark.b1, BMark.b1] CarryMotifWitnessFlow :=
    subflow_mem hSub (List.Mem.head [])
  change
    List.Mem [BMark.b1, BMark.b1]
      [[BMark.b0], [BMark.b1], [BMark.b0, BMark.b1]] at hMem
  cases hMem with
  | tail _ hTail =>
      cases hTail with
      | tail _ hTail2 =>
          cases hTail2 with
          | tail _ hNil =>
              cases hNil

theorem completion_certificate_absent_from_seal_witness :
    Not (CompletionStructure SealMotifWitnessFlow) := by
  intro hSub
  have hMem : List.Mem [BMark.b1, BMark.b1, BMark.b1]
      SealMotifWitnessFlow :=
    subflow_mem hSub (List.Mem.head [])
  change
    List.Mem [BMark.b1, BMark.b1, BMark.b1]
      [[BMark.b0], [BMark.b0, BMark.b1], [BMark.b1]] at hMem
  cases hMem with
  | tail _ hTail =>
      cases hTail with
      | tail _ hTail2 =>
          cases hTail2 with
          | tail _ hNil =>
              cases hNil

theorem recognized_carry_motif_not_dimension_lift :
    exists R S M preNormal normal ledgerFlow : EventFlow,
      CarryMotif R S M preNormal normal ledgerFlow /\
        Not (DimensionLiftStructure S) := by
  refine
    ⟨[], CarryMotifWitnessFlow, CarryMotifWitnessFlow, [[BMark.b0]],
      [[BMark.b1]], [[BMark.b0, BMark.b1]], ?_,
      dimension_lift_certificate_absent_from_carry_witness⟩
  constructor
  · exact
      ⟨FormalCompilerInput.eventFlow [],
        ⟨FormalCompilerInput.eventFlow CarryMotifWitnessFlow,
          FormalCompilerInput.eventFlow CarryMotifWitnessFlow,
          FormalCompilerInput.eventFlow CarryRole⟩,
        Or.inl ⟨[], [], rfl⟩⟩
  · constructor
    · exact Or.inl ⟨[], [[BMark.b1], [BMark.b0, BMark.b1]], rfl⟩
    · constructor
      · exact Or.inl ⟨[[BMark.b0]], [[BMark.b0, BMark.b1]], rfl⟩
      · constructor
        · exact Or.inl ⟨[[BMark.b0], [BMark.b1]], [], rfl⟩
        · constructor
          · exact ⟨[BMark.b0], [], rfl⟩
          · constructor
            · exact ⟨[BMark.b1], [], rfl⟩
            · exact ⟨[BMark.b0, BMark.b1], [], rfl⟩

theorem recognized_seal_motif_not_completion :
    exists R S M stages boundary sealFlow ledgerFlow : EventFlow,
      SealMotif R S M stages boundary sealFlow ledgerFlow /\
        Not (CompletionStructure S) := by
  refine
    ⟨[], SealMotifWitnessFlow, SealMotifWitnessFlow, [[BMark.b0]],
      [[BMark.b0, BMark.b1]], [[BMark.b1]], [[BMark.b0]], ?_,
      completion_certificate_absent_from_seal_witness⟩
  constructor
  · exact
      ⟨FormalCompilerInput.eventFlow [],
        ⟨FormalCompilerInput.eventFlow SealMotifWitnessFlow,
          FormalCompilerInput.eventFlow SealMotifWitnessFlow,
          FormalCompilerInput.eventFlow SealRole⟩,
        Or.inl ⟨[], [], rfl⟩⟩
  · constructor
    · exact Or.inl ⟨[], [[BMark.b0, BMark.b1], [BMark.b1]], rfl⟩
    · constructor
      · exact Or.inl ⟨[[BMark.b0]], [[BMark.b1]], rfl⟩
      · constructor
        · exact Or.inl ⟨[[BMark.b0], [BMark.b0, BMark.b1]], [], rfl⟩
        · constructor
          · exact Or.inl ⟨[], [[BMark.b0, BMark.b1], [BMark.b1]], rfl⟩
          · constructor
            · exact ⟨[BMark.b1], [], rfl⟩
            · exact ⟨[BMark.b0], [], rfl⟩

structure P3AuditChecklist where
  p2AuditRequirements : Prop
  candidateRecognizedSeparated : Prop
  recognizedMotifsRequireGeneratedRecognizers : Prop
  recognizedMotifsRequireLedgers : Prop
  missingRecognizersReportedUndefined : Prop
  sourceMotifsSeparatedFromChannelSubstrings : Prop
  highRiskMotifsHaveCannotClaimAnnotations : Prop
  noDerivedInterfaceLicensed : Prop
  noObjectEqualityAsserted : Prop
  noTheoremhoodAsserted : Prop
  noHardcodedMotifTableAsFormalInput : Prop
  implementationRecognizersHaveBootstrapObligations : Prop

theorem p3_adequacy
    {Rfam : GeneratedMotifRecognizer -> Prop} {S : EventFlow}
    {candidates : List EventFlow} {recognized : List MotifProfileItem} :
    SoundMotifReport Rfam S candidates recognized ->
      P3AuditChecklist ->
        (forall item : MotifProfileItem,
          List.Mem item recognized ->
            exists R : GeneratedMotifRecognizer,
              Rfam R /\ RecognizesMotif R S item.2.1 item.1 /\
                MotifLedger R S item.2.1 item.1 item.2.2) ->
          SoundMotifReport Rfam S candidates recognized /\
            exists _checklist : P3AuditChecklist,
              forall item : MotifProfileItem,
                List.Mem item recognized ->
                  exists R : GeneratedMotifRecognizer,
                    Rfam R /\ RecognizesMotif R S item.2.1 item.1 /\
                      MotifLedger R S item.2.1 item.1 item.2.2 := by
  intro hSound hChecklist hBacked
  exact ⟨hSound, hChecklist, hBacked⟩

theorem p3_conservative_over_finite_kernel
    {Rfam : GeneratedMotifRecognizer -> Prop} {S : EventFlow}
    {candidates : List EventFlow} {recognized : List MotifProfileItem}
    {R M mu : EventFlow} {w : RawEvent} {m : DisplayAlphabet} :
    SoundMotifReport Rfam S candidates recognized ->
      RecognizesMotif R S M mu ->
        List.Mem w S ->
          List.Mem m w ->
            m = BMark.b0 \/ m = BMark.b1 := by
  intro _ hRecognized hEvent hMark
  exact motif_generated_conservativity hRecognized hEvent hMark

end BEDC.GroundCompiler.MotifReportPrototype
