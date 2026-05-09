import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.PackageGenerated
import BEDC.GroundCompiler.NameCertGenerated

namespace BEDC.GroundCompiler.PackageNameCertPrototype

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

inductive P5FormalInput : Type where
  | channel (c : List DisplayAlphabet) (h : LegalZStream c)
  | eventFlow (S : EventFlow)

def GeneratedPackageRecognizer : Type :=
  BEDC.GroundCompiler.PackageGenerated.GeneratedPackageRecognizer

def GeneratedNameCertRecognizer : Type :=
  BEDC.GroundCompiler.NameCertGenerated.GeneratedNameCertRecognizer

inductive P5ReportDatum : Type where
  | decodedEventFlow (S : EventFlow)
  | packageCandidate (ambient candidate : EventFlow)
  | recognizedPackage (R : GeneratedPackageRecognizer) (S : EventFlow)
  | packageLedger (R : GeneratedPackageRecognizer) (S ledger : EventFlow)
  | nameCandidate (N : EventFlow)
  | nameCertCandidate (C N : EventFlow)
  | recognizedNameCert (R : GeneratedNameCertRecognizer) (C N : EventFlow)
  | nameCertField
      (R : GeneratedNameCertRecognizer)
      (C : EventFlow)
      (role : BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole)
      (part : EventFlow)
  | missingPackageField (candidate : EventFlow)
  | missingNameCertField (candidate name : EventFlow)
  | cannotClaim (datum : EventFlow)

def P5Output : Type :=
  List P5ReportDatum

def PackageReport : Type :=
  P5Output

inductive P5Artifact : Type where
  | input (x : P5FormalInput)
  | output (x : P5Output)

structure PkgNameCertPrototype : Type where
  run : P5FormalInput -> P5Output
  packageRecognizer : GeneratedPackageRecognizer
  nameCertRecognizer : GeneratedNameCertRecognizer
  rejectsHostObjects :
    Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert)

theorem p5_channel_input_decodes {c : List DisplayAlphabet} :
    LegalZStream c -> exists S : EventFlow, Decode c = some S := by
  intro hLegal
  cases hLegal with
  | intro S hS =>
      exact ⟨S, by rw [hS]; exact flow_level_round_trip S⟩

theorem p5_no_package_object_input :
    Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
  · exact structural_hidden_not_formal StructuralHiddenInput.hostNameCert

def PackageCandidate (S P : EventFlow) : Prop :=
  BEDC.GroundCompiler.NameCertGenerated.SourceSubflow P S

def RecognizedPackageFlow
    (R : GeneratedPackageRecognizer) (S P : EventFlow) : Prop :=
  PackageCandidate S P /\
    BEDC.GroundCompiler.PackageGenerated.PackageRecognitionRelation R P

inductive PackageRoleKind : Type where
  | source
  | visible
  | pattern
  | classifier
  | ledger
  | seal

def PackageRoleSubflow
    (R : GeneratedPackageRecognizer) (S P part : EventFlow)
    (_role : PackageRoleKind) : Prop :=
  RecognizedPackageFlow R S P /\
    PackageCandidate P part /\
    NonemptyEventFlow part

def CompletePackageRecognition
    (R : GeneratedPackageRecognizer) (S P : EventFlow) : Prop :=
  exists source visible pattern classifier ledger sealFlow : EventFlow,
    PackageRoleSubflow R S P source PackageRoleKind.source /\
      PackageRoleSubflow R S P visible PackageRoleKind.visible /\
      PackageRoleSubflow R S P pattern PackageRoleKind.pattern /\
      PackageRoleSubflow R S P classifier PackageRoleKind.classifier /\
      PackageRoleSubflow R S P ledger PackageRoleKind.ledger /\
      PackageRoleSubflow R S P sealFlow PackageRoleKind.seal

def PackageHasLedger
    (R : GeneratedPackageRecognizer) (S P : EventFlow) : Prop :=
  exists ledger : EventFlow,
    PackageRoleSubflow R S P ledger PackageRoleKind.ledger

def MissingPackageRole
    (R : GeneratedPackageRecognizer) (S P : EventFlow) : Prop :=
  (forall source : EventFlow,
    Not (PackageRoleSubflow R S P source PackageRoleKind.source)) \/
  (forall visible : EventFlow,
    Not (PackageRoleSubflow R S P visible PackageRoleKind.visible)) \/
  (forall pattern : EventFlow,
    Not (PackageRoleSubflow R S P pattern PackageRoleKind.pattern)) \/
  (forall classifier : EventFlow,
    Not (PackageRoleSubflow R S P classifier PackageRoleKind.classifier)) \/
  (forall ledger : EventFlow,
    Not (PackageRoleSubflow R S P ledger PackageRoleKind.ledger)) \/
  (forall sealFlow : EventFlow,
    Not (PackageRoleSubflow R S P sealFlow PackageRoleKind.seal))

def VisibleOnlyPackageEvidence
    (R : GeneratedPackageRecognizer) (S P visible : EventFlow) : Prop :=
  PackageRoleSubflow R S P visible PackageRoleKind.visible /\
    (forall source : EventFlow,
      Not (PackageRoleSubflow R S P source PackageRoleKind.source)) /\
    (forall pattern : EventFlow,
      Not (PackageRoleSubflow R S P pattern PackageRoleKind.pattern)) /\
    (forall classifier : EventFlow,
      Not (PackageRoleSubflow R S P classifier PackageRoleKind.classifier)) /\
    (forall ledger : EventFlow,
      Not (PackageRoleSubflow R S P ledger PackageRoleKind.ledger)) /\
    (forall sealFlow : EventFlow,
      Not (PackageRoleSubflow R S P sealFlow PackageRoleKind.seal))

theorem complete_package_recognition_has_ledger
    {R : GeneratedPackageRecognizer} {S P : EventFlow} :
    CompletePackageRecognition R S P -> PackageHasLedger R S P := by
  intro hComplete
  cases hComplete with
  | intro source hComplete =>
      cases hComplete with
      | intro visible hComplete =>
          cases hComplete with
          | intro pattern hComplete =>
              cases hComplete with
              | intro classifier hComplete =>
                  cases hComplete with
                  | intro ledger hComplete =>
                      cases hComplete with
                      | intro sealFlow hFields =>
                          exact
                            ⟨ledger, hFields.right.right.right.right.left⟩

theorem incomplete_package_not_package
    {R : GeneratedPackageRecognizer} {S P : EventFlow} :
    MissingPackageRole R S P -> Not (CompletePackageRecognition R S P) := by
  intro hMissing hComplete
  cases hComplete with
  | intro source hComplete =>
      cases hComplete with
      | intro visible hComplete =>
          cases hComplete with
          | intro pattern hComplete =>
              cases hComplete with
              | intro classifier hComplete =>
                  cases hComplete with
                  | intro ledger hComplete =>
                      cases hComplete with
                      | intro sealFlow hFields =>
                          cases hMissing with
                          | inl hNoSource =>
                              exact hNoSource source hFields.left
                          | inr hMissing =>
                              cases hMissing with
                              | inl hNoVisible =>
                                  exact hNoVisible visible hFields.right.left
                              | inr hMissing =>
                                  cases hMissing with
                                  | inl hNoPattern =>
                                      exact hNoPattern pattern
                                        hFields.right.right.left
                                  | inr hMissing =>
                                      cases hMissing with
                                      | inl hNoClassifier =>
                                          exact hNoClassifier classifier
                                            hFields.right.right.right.left
                                      | inr hMissing =>
                                          cases hMissing with
                                          | inl hNoLedger =>
                                              exact hNoLedger ledger
                                                hFields.right.right.right.right.left
                                          | inr hNoSeal =>
                                              exact hNoSeal sealFlow
                                                hFields.right.right.right.right.right

theorem visible_token_alone_not_package
    {R : GeneratedPackageRecognizer} {S P visible : EventFlow} :
    VisibleOnlyPackageEvidence R S P visible ->
      Not (CompletePackageRecognition R S P) := by
  intro hVisibleOnly
  exact incomplete_package_not_package (Or.inl hVisibleOnly.right.left)

theorem package_report_output_not_input
    (report : PackageReport) (input : P5FormalInput) :
    Not (P5Artifact.output report = P5Artifact.input input) := by
  intro h
  cases h

theorem package_candidate_has_ambient_decomposition
    {S P : EventFlow} :
    PackageCandidate S P ->
      exists before after : EventFlow,
        S = List.append before (List.append P after) := by
  intro h
  exact h

def NameCandidate (S N : EventFlow) : Prop :=
  BEDC.GroundCompiler.NameCertGenerated.SourceSubflow N S

def NameCertCandidate (S C N : EventFlow) : Prop :=
  NameCandidate S N /\
    BEDC.GroundCompiler.NameCertGenerated.SourceSubflow C S

def RecognizedNameCertFlow
    (R : GeneratedNameCertRecognizer) (S C N : EventFlow) : Prop :=
  NameCertCandidate S C N /\
    BEDC.GroundCompiler.NameCertGenerated.NameCertRecognitionRelation R C N

inductive NameCertSubflowRole : Type where
  | source
  | pattern
  | classifier
  | stability
  | ledger
  | seal

def NameCertFieldSubflow
    (R : GeneratedNameCertRecognizer) (S C N part : EventFlow)
    (role : NameCertSubflowRole) : Prop :=
  RecognizedNameCertFlow R S C N /\
    match role with
    | NameCertSubflowRole.source =>
        BEDC.GroundCompiler.NameCertGenerated.NameCertFieldSubflow R C
          BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole.source part
    | NameCertSubflowRole.pattern =>
        BEDC.GroundCompiler.NameCertGenerated.NameCertFieldSubflow R C
          BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole.pattern part
    | NameCertSubflowRole.classifier =>
        BEDC.GroundCompiler.NameCertGenerated.NameCertFieldSubflow R C
          BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole.classifier part
    | NameCertSubflowRole.stability =>
        BEDC.GroundCompiler.NameCertGenerated.NameCertFieldSubflow R C
          BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole.stability part
    | NameCertSubflowRole.ledger =>
        BEDC.GroundCompiler.NameCertGenerated.NameCertFieldSubflow R C
          BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole.ledger part
    | NameCertSubflowRole.seal =>
        BEDC.GroundCompiler.NameCertGenerated.NameCertSealSubflow R C part

def CompleteNameCertRecognition
    (R : GeneratedNameCertRecognizer) (S C N : EventFlow) : Prop :=
  exists source pattern classifier stability ledger sealFlow : EventFlow,
    NameCertFieldSubflow R S C N source NameCertSubflowRole.source /\
      NameCertFieldSubflow R S C N pattern NameCertSubflowRole.pattern /\
      NameCertFieldSubflow R S C N classifier NameCertSubflowRole.classifier /\
      NameCertFieldSubflow R S C N stability NameCertSubflowRole.stability /\
      NameCertFieldSubflow R S C N ledger NameCertSubflowRole.ledger /\
      NameCertFieldSubflow R S C N sealFlow NameCertSubflowRole.seal

def MissingNameCertRole
    (R : GeneratedNameCertRecognizer) (S C N : EventFlow) : Prop :=
  (forall source : EventFlow,
    Not (NameCertFieldSubflow R S C N source NameCertSubflowRole.source)) \/
  (forall pattern : EventFlow,
    Not (NameCertFieldSubflow R S C N pattern NameCertSubflowRole.pattern)) \/
  (forall classifier : EventFlow,
    Not (NameCertFieldSubflow R S C N classifier
      NameCertSubflowRole.classifier)) \/
  (forall stability : EventFlow,
    Not (NameCertFieldSubflow R S C N stability
      NameCertSubflowRole.stability)) \/
  (forall ledger : EventFlow,
    Not (NameCertFieldSubflow R S C N ledger NameCertSubflowRole.ledger)) \/
  (forall sealFlow : EventFlow,
    Not (NameCertFieldSubflow R S C N sealFlow NameCertSubflowRole.seal))

def LicensedNameP5Witness (S C N : EventFlow) : Prop :=
  exists R : GeneratedNameCertRecognizer, CompleteNameCertRecognition R S C N

def LicensedNameP5 (S N : EventFlow) : Prop :=
  exists C : EventFlow, LicensedNameP5Witness S C N

theorem name_event_alone_not_license
    {S N : EventFlow} :
    (forall C : EventFlow, Not (LicensedNameP5Witness S C N)) ->
      Not (LicensedNameP5 S N) := by
  intro hNoWitness hLicensed
  cases hLicensed with
  | intro C hWitness =>
      exact hNoWitness C hWitness

theorem missing_namecert_role_not_complete
    {R : GeneratedNameCertRecognizer} {S C N : EventFlow} :
    MissingNameCertRole R S C N ->
      Not (CompleteNameCertRecognition R S C N) := by
  intro hMissing hComplete
  cases hComplete with
  | intro source hComplete =>
      cases hComplete with
      | intro pattern hComplete =>
          cases hComplete with
          | intro classifier hComplete =>
              cases hComplete with
              | intro stability hComplete =>
                  cases hComplete with
                  | intro ledger hComplete =>
                      cases hComplete with
                      | intro sealFlow hFields =>
                          cases hMissing with
                          | inl hNoSource =>
                              exact hNoSource source hFields.left
                          | inr hMissing =>
                              cases hMissing with
                              | inl hNoPattern =>
                                  exact hNoPattern pattern hFields.right.left
                              | inr hMissing =>
                                  cases hMissing with
                                  | inl hNoClassifier =>
                                      exact hNoClassifier classifier
                                        hFields.right.right.left
                                  | inr hMissing =>
                                      cases hMissing with
                                      | inl hNoStability =>
                                          exact hNoStability stability
                                            hFields.right.right.right.left
                                      | inr hMissing =>
                                          cases hMissing with
                                          | inl hNoLedger =>
                                              exact hNoLedger ledger
                                                hFields.right.right.right.right.left
                                          | inr hNoSeal =>
                                              exact hNoSeal sealFlow
                                                hFields.right.right.right.right.right

theorem incomplete_namecert_candidate_cannot_license
    {S C N : EventFlow} :
    (forall R : GeneratedNameCertRecognizer, MissingNameCertRole R S C N) ->
      Not (LicensedNameP5Witness S C N) := by
  intro hIncomplete hLicense
  cases hLicense with
  | intro R hComplete =>
      exact missing_namecert_role_not_complete (hIncomplete R) hComplete

theorem no_namecert_without_five_fields
    {R : GeneratedNameCertRecognizer} {S C N : EventFlow} :
    RecognizedNameCertFlow R S C N ->
      CompleteNameCertRecognition R S C N := by
  intro hRecognized
  cases hRecognized.right.right.right with
  | intro source hComplete =>
      cases hComplete with
      | intro pattern hComplete =>
          cases hComplete with
          | intro classifier hComplete =>
              cases hComplete with
              | intro stability hComplete =>
                  cases hComplete with
                  | intro ledger hComplete =>
                      cases hComplete with
                      | intro sealFlow hFields =>
                          exact
                            ⟨source, pattern, classifier, stability, ledger,
                              sealFlow,
                              ⟨hRecognized, hFields.left⟩,
                              ⟨hRecognized, hFields.right.left⟩,
                              ⟨hRecognized, hFields.right.right.left⟩,
                              ⟨hRecognized, hFields.right.right.right.left⟩,
                              ⟨hRecognized,
                                hFields.right.right.right.right.left⟩,
                              ⟨hRecognized,
                                hFields.right.right.right.right.right⟩⟩

def NameCertOverPackage
    (Rpkg : GeneratedPackageRecognizer) (Rn : GeneratedNameCertRecognizer)
    (S C N P : EventFlow) : Prop :=
  RecognizedPackageFlow Rpkg S P /\
    PackageHasLedger Rpkg S P /\
    RecognizedNameCertFlow Rn S C N

theorem namecert_over_package_requires_ledger
    {Rpkg : GeneratedPackageRecognizer} {Rn : GeneratedNameCertRecognizer}
    {S C N P : EventFlow} :
    NameCertOverPackage Rpkg Rn S C N P -> PackageHasLedger Rpkg S P := by
  intro hOver
  exact hOver.right.left

theorem package_without_ledger_no_namecert_over_package
    {Rpkg : GeneratedPackageRecognizer} {S P : EventFlow} :
    Not (PackageHasLedger Rpkg S P) ->
      Not (exists Rn : GeneratedNameCertRecognizer,
        exists C N : EventFlow, NameCertOverPackage Rpkg Rn S C N P) := by
  intro hNoLedger hOver
  cases hOver with
  | intro Rn hRn =>
      cases hRn with
      | intro C hC =>
          cases hC with
          | intro N hNameCertOver =>
              exact hNoLedger
                (namecert_over_package_requires_ledger hNameCertOver)

structure PackageSourcedNameCertReport : Type where
  packageRecognizer : GeneratedPackageRecognizer
  nameCertRecognizer : GeneratedNameCertRecognizer
  ambientFlow : EventFlow
  nameCertFlow : EventFlow
  nameCandidate : EventFlow
  packageFlow : EventFlow
  overPackage :
    NameCertOverPackage packageRecognizer nameCertRecognizer
      ambientFlow nameCertFlow nameCandidate packageFlow
  missingFieldReport : P5Output
  cannotClaimAnnotations : P5Output

inductive FieldStatus : Type where
  | present
  | missing
  | candidateOnly

def PackageFieldStatus : Type :=
  EventFlow -> PackageRoleKind -> FieldStatus

def NameCertFieldStatus : Type :=
  EventFlow -> NameCertSubflowRole -> FieldStatus

structure P5Report : Type where
  outputView : P5Output
  decodedFlow : EventFlow
  packageFieldStatus : PackageFieldStatus
  nameCertFieldStatus : NameCertFieldStatus
  licensedNameStatus : EventFlow -> EventFlow -> Prop
  cannotClaimAnnotation : EventFlow -> Prop

structure SoundP5Report (report : P5Report) : Prop where
  packageSupport :
    forall R : GeneratedPackageRecognizer,
      forall P : EventFlow,
        List.Mem (P5ReportDatum.recognizedPackage R P) report.outputView ->
          RecognizedPackageFlow R report.decodedFlow P /\
            PackageHasLedger R report.decodedFlow P
  nameCertSupport :
    forall R : GeneratedNameCertRecognizer,
      forall C N : EventFlow,
        List.Mem (P5ReportDatum.recognizedNameCert R C N) report.outputView ->
          RecognizedNameCertFlow R report.decodedFlow C N /\
            exists ledger : EventFlow,
              NameCertFieldSubflow R report.decodedFlow C N ledger
                NameCertSubflowRole.ledger

theorem sound_p5_report {report : P5Report} :
    SoundP5Report report ->
      (forall R : GeneratedPackageRecognizer,
        forall P : EventFlow,
          List.Mem (P5ReportDatum.recognizedPackage R P) report.outputView ->
            RecognizedPackageFlow R report.decodedFlow P /\
              PackageHasLedger R report.decodedFlow P) /\
      (forall R : GeneratedNameCertRecognizer,
        forall C N : EventFlow,
          List.Mem (P5ReportDatum.recognizedNameCert R C N) report.outputView ->
            RecognizedNameCertFlow R report.decodedFlow C N /\
              exists ledger : EventFlow,
                NameCertFieldSubflow R report.decodedFlow C N ledger
                  NameCertSubflowRole.ledger) := by
  intro hSound
  constructor
  · intro R P hMem
    exact hSound.packageSupport R P hMem
  · intro R C N hMem
    exact hSound.nameCertSupport R C N hMem

theorem p5_license_weaker_than_export :
    exists S N : EventFlow, LicensedNameP5 S N /\ Not (AcceptedObjectFlow S) := by
  have hSubflow :
      BEDC.GroundCompiler.NameCertGenerated.SourceSubflow
        ([] : EventFlow) ([] : EventFlow) :=
    ⟨[], [], rfl⟩
  have hRecognizes :
      RecognizesNameCert ([] : GeneratedNameCertRecognizer) ([] : EventFlow) :=
    FormalCompilerInput.recognizedFlow [] []
  have hGeneratedComplete :
      BEDC.GroundCompiler.NameCertGenerated.CompleteFiveFieldRecognition
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow) :=
    ⟨[], [], [], [], [], [],
      ⟨hRecognizes, hSubflow⟩,
      ⟨hRecognizes, hSubflow⟩,
      ⟨hRecognizes, hSubflow⟩,
      ⟨hRecognizes, hSubflow⟩,
      ⟨hRecognizes, hSubflow⟩,
      ⟨hRecognizes, hSubflow⟩⟩
  have hRelation :
      BEDC.GroundCompiler.NameCertGenerated.NameCertRecognitionRelation
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow) ([] : EventFlow) :=
    ⟨hRecognizes, FormalCompilerInput.eventFlow [], hGeneratedComplete⟩
  have hCandidate : NameCertCandidate ([] : EventFlow) [] [] :=
    ⟨hSubflow, hSubflow⟩
  have hRecognized :
      RecognizedNameCertFlow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) :=
    ⟨hCandidate, hRelation⟩
  have hSource :
      NameCertFieldSubflow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
        NameCertSubflowRole.source :=
    ⟨hRecognized, ⟨hRecognizes, hSubflow⟩⟩
  have hPattern :
      NameCertFieldSubflow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
        NameCertSubflowRole.pattern :=
    ⟨hRecognized, ⟨hRecognizes, hSubflow⟩⟩
  have hClassifier :
      NameCertFieldSubflow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
        NameCertSubflowRole.classifier :=
    ⟨hRecognized, ⟨hRecognizes, hSubflow⟩⟩
  have hStability :
      NameCertFieldSubflow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
        NameCertSubflowRole.stability :=
    ⟨hRecognized, ⟨hRecognizes, hSubflow⟩⟩
  have hLedger :
      NameCertFieldSubflow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
        NameCertSubflowRole.ledger :=
    ⟨hRecognized, ⟨hRecognizes, hSubflow⟩⟩
  have hSeal :
      NameCertFieldSubflow
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) ([] : EventFlow)
        NameCertSubflowRole.seal :=
    ⟨hRecognized, ⟨hRecognizes, hSubflow⟩⟩
  have hComplete :
      CompleteNameCertRecognition
        ([] : GeneratedNameCertRecognizer) ([] : EventFlow)
        ([] : EventFlow) ([] : EventFlow) :=
    ⟨[], [], [], [], [], [], hSource, hPattern, hClassifier, hStability,
      hLedger, hSeal⟩
  exact
    ⟨[], [],
      ⟨⟨[], ⟨[], hComplete⟩⟩, empty_not_accepted_object_flow⟩⟩

end BEDC.GroundCompiler.PackageNameCertPrototype
