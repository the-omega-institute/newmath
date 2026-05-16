import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_located_real_completion_handoff [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      criterionTolerance criterionRegseq criterionTransport criterionRoute criterionEndpoint sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg →
      BEDC.Derived.CauchyCriterionUp.CauchyCriterionCarrier schedule modulus
          criterionTolerance ledger criterionRegseq realSeal criterionTransport criterionRoute
          provenance nameRow criterionEndpoint bundle pkg →
        Cont ledger interval sealRead →
          Cont sealRead criterionEndpoint publicRead →
            PkgSig bundle sealRead pkg →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal
                      transportRow route provenance nameRow bundle pkg ∧ hsame row publicRead)
                  (fun row : BHist =>
                    Cont schedule modulus criterionTolerance ∧
                      Cont criterionTolerance ledger criterionRegseq ∧
                        Cont ledger interval sealRead ∧
                          Cont sealRead criterionEndpoint row)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro monotone criterion ledgerIntervalSeal sealEndpointPublic _sealPkg publicPkg
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    realSealUnary, transportRowUnary, routeUnary, provenanceUnary, nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := monotone
  obtain ⟨_scheduleUnary, _modulusUnary, criterionToleranceUnary, _ledgerUnary,
    criterionRegseqUnary, _realSealUnary, criterionTransportUnary, criterionRouteUnary,
    _provenanceUnary, _localCertUnary, criterionEndpointUnary, scheduleModulusTolerance,
    toleranceLedgerRegseq, _regseqRealSealTransport, _transportLocalCertRoute,
    _routeProvenanceEndpoint, _criterionEndpointPkg⟩ := criterion
  have monotonePacket :
      MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal
        transportRow route provenance nameRow bundle pkg :=
    ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary, realSealUnary,
      transportRowUnary, routeUnary, provenanceUnary, nameRowUnary, regularScheduleModulus,
      modulusLedgerInterval, intervalRealSealNameRow, transportRouteProvenance, nameRowPkg⟩
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary intervalUnary ledgerIntervalSeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary criterionEndpointUnary sealEndpointPublic
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro monotonePacket (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨scheduleModulusTolerance, toleranceLedgerRegseq, ledgerIntervalSeal,
          cont_result_hsame_transport sealEndpointPublic (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport publicReadUnary (hsame_symm source.right), publicPkg⟩
  }

end BEDC.Derived.MonotoneCauchyUp
