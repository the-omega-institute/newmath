import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_externality_handoff [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow boundaryRead →
        Cont boundaryRead provenance handoffRead →
          PkgSig bundle handoffRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row handoffRead)
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun _row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory handoffRead ∧ Cont socket request gate ∧
                    Cont gate ledger nameRow ∧ Cont ledger nameRow boundaryRead ∧
                      Cont boundaryRead provenance handoffRead ∧
                        hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier boundaryRoute handoffRoute handoffPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary boundaryRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed boundaryUnary provenanceUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row handoffRead)
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro handoffRead ⟨carrierPacket, hsame_refl handoffRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport handoffUnary (hsame_symm source.right)⟩
    · intro _row _source
      exact ⟨provenancePkg, handoffPkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, provenanceUnary,
      boundaryUnary, handoffUnary, socketRequestGate, gateLedgerNameRow, boundaryRoute,
      handoffRoute, ledgerSameRequestGate, provenancePkg, handoffPkg⟩

end BEDC.Derived.ApophaticNameUp
