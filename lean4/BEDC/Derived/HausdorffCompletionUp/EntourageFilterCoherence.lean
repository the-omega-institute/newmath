import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_entourage_filter_coherence [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont source handoff sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                HausdorffCompletionCarrier source entourage separated handoff transport route
                    provenance bundle pkg ∧ hsame row sealRead)
              (fun row : BHist =>
                hsame row sealRead ∧ UnaryHistory row ∧ Cont source entourage transport ∧
                  Cont transport route provenance)
              (fun _row : BHist =>
                PkgSig bundle sealRead pkg ∧ PkgSig bundle provenance pkg ∧
                  Cont source handoff sealRead)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory handoff ∧
              UnaryHistory sealRead ∧ Cont source entourage transport ∧
                Cont source handoff sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceHandoffSeal sealPkg
  have carrierPacket :
      HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg :=
    carrier
  obtain ⟨sourceUnary, entourageUnary, _separatedUnary, handoffUnary, _transportUnary,
    _routeUnary, _provenanceUnary, sourceEntourageTransport, _separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary handoffUnary sourceHandoffSeal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HausdorffCompletionCarrier source entourage separated handoff transport route
                provenance bundle pkg ∧ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ UnaryHistory row ∧ Cont source entourage transport ∧
              Cont transport route provenance)
          (fun _row : BHist =>
            PkgSig bundle sealRead pkg ∧ PkgSig bundle provenance pkg ∧
              Cont source handoff sealRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead ⟨carrierPacket, hsame_refl sealRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        exact
          ⟨sourceRow.right, unary_transport sealUnary (hsame_symm sourceRow.right),
            sourceEntourageTransport, transportRouteProvenance⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨sealPkg, provenancePkg, sourceHandoffSeal⟩
    }
  exact
    ⟨cert, sourceUnary, entourageUnary, handoffUnary, sealUnary, sourceEntourageTransport,
      sourceHandoffSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.HausdorffCompletionUp
