import BEDC.GroundCompiler.MotifReportCounts

namespace BEDC.GroundCompiler.MotifReportPrototype

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

end BEDC.GroundCompiler.MotifReportPrototype
