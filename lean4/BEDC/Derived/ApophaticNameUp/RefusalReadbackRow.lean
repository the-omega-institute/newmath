import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_readback_row [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow imageRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont socket request imageRead ->
        PkgSig bundle imageRead pkg ->
          Cont imageRead nameRow readbackRead ->
            PkgSig bundle readbackRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg /\ hsame row imageRead)
                (fun row : BHist => hsame row imageRead /\ UnaryHistory row)
                (fun row : BHist =>
                  PkgSig bundle imageRead pkg /\ PkgSig bundle readbackRead pkg /\
                    hsame row imageRead /\ Cont imageRead nameRow readbackRead)
                hsame /\
              UnaryHistory imageRead /\ UnaryHistory readbackRead /\
                Cont socket request imageRead /\ Cont imageRead nameRow readbackRead /\
                  PkgSig bundle imageRead pkg /\ PkgSig bundle readbackRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestImage imagePkg imageNameReadback readbackPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    _gateLedgerNameRow, _ledgerSameRequestGate, _provenancePkg⟩ := carrier
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed socketUnary requestUnary socketRequestImage
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed imageUnary nameRowUnary imageNameReadback
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance
            nameRow bundle pkg /\ hsame row imageRead)
        (fun row : BHist => hsame row imageRead /\ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle imageRead pkg /\ PkgSig bundle readbackRead pkg /\
            hsame row imageRead /\ Cont imageRead nameRow readbackRead)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro imageRead ⟨carrierPacket, hsame_refl imageRead⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact
        ⟨source.right, unary_transport imageUnary (hsame_symm source.right)⟩
    · intro row source
      exact ⟨imagePkg, readbackPkg, source.right, imageNameReadback⟩
  exact
    ⟨cert, imageUnary, readbackUnary, socketRequestImage, imageNameReadback, imagePkg,
      readbackPkg⟩

end BEDC.Derived.ApophaticNameUp
