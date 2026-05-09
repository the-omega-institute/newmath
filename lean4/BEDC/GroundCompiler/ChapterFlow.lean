import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.ChapterFlow

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def ChapterCandidateFlow : Type :=
  EventFlow

def GeneratedChapterRecognizer : Type :=
  EventFlow

def RecognizesChapter
    (R : GeneratedChapterRecognizer) (C : ChapterCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R C) /\
    NonemptyEventFlow C

def ChapterFlow (C : ChapterCandidateFlow) : Prop :=
  exists R : GeneratedChapterRecognizer, RecognizesChapter R C

def ChapterCode (C : ChapterCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding C

theorem no_external_chapter_input :
    Not (FormalCompilerInput CompilerDatum.hostChapterPkg) :=
  structural_hidden_not_formal StructuralHiddenInput.hostChapterPkg

theorem chapter_recognition_preserves_code
    {R : GeneratedChapterRecognizer} {C : ChapterCandidateFlow} :
    RecognizesChapter R C -> ChapterCode C = FlowEncoding C := by
  intro _
  rfl

theorem chapter_code_not_new_code {C : ChapterCandidateFlow} :
    ChapterFlow C -> ChapterCode C = FlowEncoding C := by
  intro _
  rfl

end BEDC.GroundCompiler.ChapterFlow
