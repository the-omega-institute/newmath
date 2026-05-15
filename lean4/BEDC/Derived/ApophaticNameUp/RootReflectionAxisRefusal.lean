import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_reflection_axis_refusal [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow reflectionRead classifierRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow reflectionRead →
        Cont ledger nameRow classifierRead →
          PkgSig bundle reflectionRead pkg →
            PkgSig bundle classifierRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row ledger)
                  (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ hsame row (append request gate) ∧
                      Cont gate ledger nameRow)
                  hsame ∧
                UnaryHistory reflectionRead ∧ UnaryHistory classifierRead ∧
                  Cont ledger nameRow reflectionRead ∧ Cont ledger nameRow classifierRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle reflectionRead pkg ∧
                      PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameReflection ledgerNameClassifier reflectionPkg classifierPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ :=
    carrier
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameReflection
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameClassifier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row (append request gate) ∧
              Cont gate ledger nameRow)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameLedger : hsame row ledger := source.right
      exact
        ⟨hsame_trans rowSameLedger ledgerSameRequestGate,
          unary_transport ledgerUnary (hsame_symm rowSameLedger)⟩
    · intro _row source
      have rowSameLedger : hsame _row ledger := source.right
      exact
        ⟨provenancePkg, hsame_trans rowSameLedger ledgerSameRequestGate,
          gateLedgerNameRow⟩
  exact
    ⟨cert, reflectionUnary, classifierUnary, ledgerNameReflection, ledgerNameClassifier,
      ledgerSameRequestGate, reflectionPkg, classifierPkg⟩

end BEDC.Derived.ApophaticNameUp
