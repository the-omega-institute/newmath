import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_socket_exposure [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row socket ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg)
              (fun row : BHist => hsame row socket ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket request rootRead ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory rootRead ∧
              Cont socket request rootRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestRoot rootPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed socketUnary requestUnary socketRequestRoot
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socket ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row socket ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket request rootRead ∧ PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro socket (And.intro (hsame_refl socket) carrierPacket)
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro row source
      exact ⟨source.left, unary_transport socketUnary (hsame_symm source.left)⟩
    · intro _row _source
      exact ⟨socketRequestRoot, provenancePkg⟩
  exact ⟨cert, socketUnary, requestUnary, rootUnary, socketRequestRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.ApophaticNameUp
