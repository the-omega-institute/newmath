import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_metric_uniform_compatibility [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name metricRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow transport metricRead →
        Cont sealRow transport uniformRead →
          PkgSig bundle metricRead pkg →
            PkgSig bundle uniformRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    CauchyFilterCompletionPacket filter windows tolerance readback sealRow
                        transport replay provenance name bundle pkg ∧
                      (hsame row sealRow ∨ hsame row metricRead ∨ hsame row uniformRead))
                  (fun _row : BHist =>
                    Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                      Cont sealRow transport metricRead ∧ Cont sealRow transport uniformRead ∧
                        PkgSig bundle metricRead pkg ∧ PkgSig bundle uniformRead pkg)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle metricRead pkg ∧
                      PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet metricRoute uniformRoute metricPkg uniformPkg
  have packetWhole := packet
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed sealUnary transportUnary metricRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary transportUnary uniformRoute
  have sourceSeal :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row sealRow ∨ hsame row metricRead ∨ hsame row uniformRead)) sealRow := by
    exact ⟨packetWhole, Or.inl (hsame_refl sealRow)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                replay provenance name bundle pkg ∧
              (hsame row sealRow ∨ hsame row metricRead ∨ hsame row uniformRead))
          (fun _row : BHist =>
            Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
              Cont sealRow transport metricRead ∧ Cont sealRow transport uniformRead ∧
                PkgSig bundle metricRead pkg ∧ PkgSig bundle uniformRead pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle metricRead pkg ∧
              PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceSeal
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
        cases source with
        | intro sourcePacket sourceRows =>
            constructor
            · exact sourcePacket
            · cases sourceRows with
              | inl sameSeal =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)
              | inr rest =>
                  cases rest with
                  | inl sameMetric =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameMetric))
                  | inr sameUniform =>
                      exact
                        Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameUniform))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨filterWindows, toleranceReadback, metricRoute, uniformRoute, metricPkg, uniformPkg⟩
    ledger_sound := by
      intro _row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameSeal =>
              exact
                ⟨unary_transport sealUnary (hsame_symm sameSeal), metricPkg, uniformPkg⟩
          | inr rest =>
              cases rest with
              | inl sameMetric =>
                  exact
                    ⟨unary_transport metricUnary (hsame_symm sameMetric), metricPkg,
                      uniformPkg⟩
              | inr sameUniform =>
                  exact
                    ⟨unary_transport uniformUnary (hsame_symm sameUniform), metricPkg,
                      uniformPkg⟩
  }
  exact ⟨cert, metricUnary, uniformUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
