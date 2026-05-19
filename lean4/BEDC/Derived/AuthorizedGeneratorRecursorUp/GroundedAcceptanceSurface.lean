import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_grounded_acceptance_surface [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont M D descentRead ->
          Cont branchRead descentRead outputRead ->
            Cont outputRead C publicRead ->
              UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                  PkgSig bundle P pkg ∧ hsame H (append A C) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier branchRoute descentRoute outputRoute publicRoute
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, _unaryO, _unaryA, _unaryH, unaryC,
      _unaryP, _unaryG, _unaryN, _iem, _mbd, _doa, sameTransport, pkgSig⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed unaryM unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed branchUnary descentUnary outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary unaryC publicRoute
  exact ⟨branchUnary, descentUnary, outputUnary, publicUnary, pkgSig, sameTransport⟩

theorem AuthorizedGeneratorRecursorReadbackProvenanceSurface [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert readback replay boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
      transport continuation provenance boundary localCert bundle pkg ->
        Cont output continuation readback ->
          Cont readback provenance replay ->
            Cont boundary localCert boundaryRead ->
              PkgSig bundle replay pkg ->
                UnaryHistory output ∧ UnaryHistory readback ∧ UnaryHistory replay ∧
                  UnaryHistory boundaryRead ∧ Cont output continuation readback ∧
                    Cont readback provenance replay ∧ Cont boundary localCert boundaryRead ∧
                      hsame transport (append audit continuation) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier outputReadback readbackReplay boundaryReadRoute replayPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, sameTransport, provenancePkg⟩
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed outputUnary continuationUnary outputReadback
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary provenanceUnary readbackReplay
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary boundaryReadRoute
  exact
    ⟨outputUnary, readbackUnary, replayUnary, boundaryReadUnary, outputReadback,
      readbackReplay, boundaryReadRoute, sameTransport, provenancePkg, replayPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
