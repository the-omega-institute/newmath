import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.ChapterFlow

open BEDC.GroundCompiler.EventFlow

def ChapterCandidateFlow : Type :=
  EventFlow

def GeneratedChapterRecognizer : Type :=
  EventFlow

def RecognizesChapter
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R C) /\
    NonemptyEventFlow C

end BEDC.GroundCompiler.ChapterFlow
