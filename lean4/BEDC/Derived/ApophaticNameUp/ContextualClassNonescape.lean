import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_contextual_class_nonescape [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow contextualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow contextualRead →
        PkgSig bundle contextualRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row nameRow)
              (fun row : BHist =>
                hsame row nameRow ∧ UnaryHistory row ∧ Cont gate ledger nameRow)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle contextualRead pkg ∧
                  hsame row nameRow ∧ Cont ledger nameRow contextualRead)
              hsame ∧
            UnaryHistory contextualRead ∧ Cont gate ledger nameRow ∧
              Cont ledger nameRow contextualRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle contextualRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameContext contextualPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have contextualUnary : UnaryHistory contextualRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameContext
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist =>
            hsame row nameRow ∧ UnaryHistory row ∧ Cont gate ledger nameRow)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle contextualRead pkg ∧
              hsame row nameRow ∧ Cont ledger nameRow contextualRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameName : hsame row nameRow := source.right
      exact
        ⟨rowSameName, unary_transport nameRowUnary (hsame_symm rowSameName),
          gateLedgerNameRow⟩
    · intro row source
      exact ⟨provenancePkg, contextualPkg, source.right, ledgerNameContext⟩
  exact
    ⟨cert, contextualUnary, gateLedgerNameRow, ledgerNameContext, provenancePkg,
      contextualPkg⟩

end BEDC.Derived.ApophaticNameUp
