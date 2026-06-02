import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_completion_handoff [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name metricRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow metricRead →
        Cont sealRow transport uniformRead →
          PkgSig bundle metricRead pkg →
            PkgSig bundle uniformRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row metricRead ∨ hsame row uniformRead)
                  (fun _row : BHist =>
                    Cont readback sealRow metricRead ∧ Cont sealRow transport uniformRead ∧
                      PkgSig bundle metricRead pkg ∧ PkgSig bundle uniformRead pkg)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle metricRead pkg ∧
                      PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet readbackSealMetric sealTransportUniform metricPkg uniformPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealMetric
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary transportUnary sealTransportUniform
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricRead ∨ hsame row uniformRead)
          (fun _row : BHist =>
            Cont readback sealRow metricRead ∧ Cont sealRow transport uniformRead ∧
              PkgSig bundle metricRead pkg ∧ PkgSig bundle uniformRead pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle metricRead pkg ∧
              PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro metricRead (Or.inl (hsame_refl metricRead))
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
        intro row other sameRows source
        cases source with
        | inl sameMetric =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameMetric)
        | inr sameUniform =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameUniform)
    }
    pattern_sound := by
      intro _row _source
      exact ⟨readbackSealMetric, sealTransportUniform, metricPkg, uniformPkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl sameMetric =>
          exact
            ⟨unary_transport metricUnary (hsame_symm sameMetric), metricPkg, uniformPkg⟩
      | inr sameUniform =>
          exact
            ⟨unary_transport uniformUnary (hsame_symm sameUniform), metricPkg, uniformPkg⟩
  }
  exact ⟨cert, metricUnary, uniformUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
