import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_named_externality_namecert_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow citation →
        PkgSig bundle citation pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row nameRow ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg)
              (fun row : BHist => hsame row nameRow ∧ UnaryHistory nameRow)
              (fun _row : BHist =>
                Cont socket request gate ∧ Cont gate ledger nameRow ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socket ∧
            UnaryHistory request ∧
            UnaryHistory gate ∧
            UnaryHistory ledger ∧
            Cont socket request gate ∧
            Cont gate ledger nameRow ∧
            Cont ledger nameRow citation ∧
            PkgSig bundle provenance pkg ∧
            PkgSig bundle citation pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameCitation citationPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameRow ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory nameRow)
          (fun _row : BHist =>
            Cont socket request gate ∧ Cont gate ledger nameRow ∧
              PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro nameRow ⟨hsame_refl nameRow, carrierPacket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro _row source
      exact ⟨source.left, nameRowUnary⟩
    · intro _row _source
      exact ⟨socketRequestGate, gateLedgerNameRow, provenancePkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, socketRequestGate,
      gateLedgerNameRow, ledgerNameCitation, provenancePkg, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
