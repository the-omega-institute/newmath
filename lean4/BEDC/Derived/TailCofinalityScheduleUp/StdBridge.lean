import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleUp_StdBridge [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont endpoint route publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport
                  route provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ Cont endpoint route publicRead)
              (fun row : BHist =>
                PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg ∧ hsame row endpoint)
              hsame ∧
            UnaryHistory publicRead ∧ Cont endpoint route publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier endpointRoutePublic publicPkg
  have carrierPacket :
      TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg :=
    carrier
  obtain ⟨_precisionUnary, _windowUnary, _dyadicUnary, _regseqUnary, _sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary routeUnary endpointRoutePublic
  have sourceEndpoint :
      (fun row : BHist =>
        TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
          provenance localCert endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact And.intro carrierPacket (hsame_refl endpoint)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
              provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ Cont endpoint route publicRead)
          (fun row : BHist =>
            PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg ∧ hsame row endpoint)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
        exact And.intro source.right endpointRoutePublic
      ledger_sound := by
        intro _row source
        exact And.intro endpointPkg (And.intro publicPkg source.right)
    }
  exact And.intro cert (And.intro publicUnary endpointRoutePublic)

end BEDC.Derived.TailCofinalityScheduleUp
