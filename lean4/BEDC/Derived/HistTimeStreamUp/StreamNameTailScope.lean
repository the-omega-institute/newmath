import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_streamname_tail_scope [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name tailRead streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay streamRead ->
        Cont streamRead name tailRead ->
          PkgSig bundle tailRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row tailRead)
                (fun row : BHist =>
                  hsame row tailRead ∧ Cont source replay streamRead ∧
                    Cont streamRead name tailRead)
                (fun row : BHist =>
                  hsame row tailRead ∧ PkgSig bundle tailRead pkg ∧ hsame provenance replay)
                hsame ∧
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory replay ∧
                UnaryHistory streamRead ∧ UnaryHistory tailRead ∧
                  Cont schedule start replay ∧ Cont source replay streamRead ∧
                    Cont streamRead name tailRead ∧ hsame provenance replay ∧
                      PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sourceReplayStream streamNameTail tailPkg
  have carrierPacket := carrier
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sourceUnary replayUnary sourceReplayStream
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed streamUnary nameUnary streamNameTail
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row tailRead)
          (fun row : BHist =>
            hsame row tailRead ∧ Cont source replay streamRead ∧
              Cont streamRead name tailRead)
          (fun row : BHist =>
            hsame row tailRead ∧ PkgSig bundle tailRead pkg ∧ hsame provenance replay)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro tailRead
          (And.intro carrierPacket (hsame_refl tailRead))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, sourceReplayStream, streamNameTail⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right, tailPkg, provenanceReplay⟩
    }
  exact
    ⟨cert, sourceUnary, scheduleUnary, replayUnary, streamUnary, tailUnary,
      scheduleStartReplay, sourceReplayStream, streamNameTail, provenanceReplay, tailPkg⟩

end BEDC.Derived.HistTimeStreamUp
