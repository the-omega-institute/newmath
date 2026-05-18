import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_visible_request_factorization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont route provenance visibleRead ->
        PkgSig bundle visibleRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row request)
              (fun row : BHist => hsame row request ∧ Cont socket request gate ∧
                UnaryHistory row)
              (fun row : BHist =>
                hsame row request ∧ hsame ledger (append request gate) ∧
                  Cont route provenance visibleRead ∧ PkgSig bundle visibleRead pkg)
              hsame ∧
            UnaryHistory visibleRead ∧ Cont socket request gate ∧
              Cont route provenance visibleRead ∧ hsame ledger (append request gate) ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle visibleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceVisible visiblePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have visibleUnary : UnaryHistory visibleRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceVisible
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row request)
          (fun row : BHist => hsame row request ∧ Cont socket request gate ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row request ∧ hsame ledger (append request gate) ∧
              Cont route provenance visibleRead ∧ PkgSig bundle visibleRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro request
          (And.intro carrierPacket (hsame_refl request))
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
        intro row source
        exact
          ⟨source.right, socketRequestGate,
            unary_transport requestUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right, ledgerSameRequestGate, routeProvenanceVisible, visiblePkg⟩
    }
  exact
    ⟨cert, visibleUnary, socketRequestGate, routeProvenanceVisible, ledgerSameRequestGate,
      provenancePkg, visiblePkg⟩

end BEDC.Derived.ApophaticNameUp
