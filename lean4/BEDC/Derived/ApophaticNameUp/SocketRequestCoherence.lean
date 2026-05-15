import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_socket_request_coherence [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate requestRead →
        PkgSig bundle requestRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row socket)
              (fun row : BHist =>
                hsame row socket ∧ UnaryHistory row ∧ Cont request gate requestRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg ∧
                  hsame row socket ∧ Cont socket request gate)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory requestRead ∧
              Cont socket request gate ∧ Cont request gate requestRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateRead requestReadPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed requestUnary gateUnary requestGateRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row socket)
          (fun row : BHist =>
            hsame row socket ∧ UnaryHistory row ∧ Cont request gate requestRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle requestRead pkg ∧
              hsame row socket ∧ Cont socket request gate)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro socket ⟨carrierPacket, hsame_refl socket⟩
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
          ⟨source.right, unary_transport socketUnary (hsame_symm source.right),
            requestGateRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, requestReadPkg, source.right, socketRequestGate⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, requestReadUnary, socketRequestGate,
      requestGateRead, provenancePkg, requestReadPkg⟩

end BEDC.Derived.ApophaticNameUp
