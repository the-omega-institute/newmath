import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_request_image_row [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow imageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request imageRead →
        PkgSig bundle imageRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row request)
              (fun row : BHist => hsame row request ∧ UnaryHistory row)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle imageRead pkg ∧
                  Cont socket request imageRead)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory imageRead ∧
              Cont socket request imageRead ∧ hsame ledger (append request gate) ∧
                PkgSig bundle imageRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestImage imagePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed socketUnary requestUnary socketRequestImage
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row request)
          (fun row : BHist => hsame row request ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle imageRead pkg ∧
              Cont socket request imageRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro request ⟨carrierPacket, hsame_refl request⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport requestUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, imagePkg, socketRequestImage⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, imageUnary, socketRequestImage,
      ledgerSameRequestGate, imagePkg⟩

theorem ApophaticNameCarrier_root_bridge_tuple_ledger [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow downstreamRead ->
        Cont downstreamRead route handoff ->
          PkgSig bundle handoff pkg ->
            UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧ UnaryHistory handoff ∧
              hsame ledger (append request gate) ∧ Cont ledger nameRow downstreamRead ∧
                Cont downstreamRead route handoff ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier ledgerNameRowDownstream downstreamRouteHandoff handoffPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRowDownstream
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed downstreamUnary routeUnary downstreamRouteHandoff
  exact
    ⟨ledgerUnary, downstreamUnary, handoffUnary, ledgerSameRequestGate,
      ledgerNameRowDownstream, downstreamRouteHandoff, provenancePkg, handoffPkg⟩

end BEDC.Derived.ApophaticNameUp
