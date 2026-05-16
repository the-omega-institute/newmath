import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_tuple_bridge_scope [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow imageRead readbackRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request imageRead →
        Cont ledger nameRow readbackRead →
          Cont readbackRead route bridgeRead →
            PkgSig bundle imageRead pkg →
              PkgSig bundle readbackRead pkg →
                PkgSig bundle bridgeRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row ledger ∧
                          ApophaticNameCarrier socket request gate ledger transport route
                            provenance nameRow bundle pkg)
                      (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
                      (fun _row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle readbackRead pkg ∧
                          PkgSig bundle bridgeRead pkg ∧ Cont ledger nameRow readbackRead)
                      hsame ∧
                    UnaryHistory imageRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory bridgeRead ∧ hsame ledger (append request gate) ∧
                        Cont ledger nameRow readbackRead ∧ Cont readbackRead route bridgeRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestImage ledgerNameReadback readbackRouteBridge _imagePkg
    readbackPkg bridgePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, ledgerUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed socketUnary requestUnary socketRequestImage
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameReadback
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteBridge
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledger ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle readbackRead pkg ∧
              PkgSig bundle bridgeRead pkg ∧ Cont ledger nameRow readbackRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨hsame_refl ledger, carrierPacket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro _row source
      exact ⟨source.left, unary_transport ledgerUnary (hsame_symm source.left)⟩
    · intro _row _source
      exact ⟨provenancePkg, readbackPkg, bridgePkg, ledgerNameReadback⟩
  exact
    ⟨cert, imageUnary, readbackUnary, bridgeUnary, ledgerSameRequestGate,
      ledgerNameReadback, readbackRouteBridge, provenancePkg, bridgePkg⟩

end BEDC.Derived.ApophaticNameUp
