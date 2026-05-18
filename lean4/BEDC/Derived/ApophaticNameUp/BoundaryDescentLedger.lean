import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_descent_ledger [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont route provenance descentRead →
        PkgSig bundle descentRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row provenance)
              (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle descentRead pkg ∧
                  hsame row provenance ∧ Cont route provenance descentRead)
              hsame ∧
            UnaryHistory descentRead ∧ Cont route provenance descentRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle descentRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceDescent descentPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceDescent
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle descentRead pkg ∧
              hsame row provenance ∧ Cont route provenance descentRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro provenance ⟨carrierPacket, hsame_refl provenance⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameProvenance : hsame row provenance := source.right
      exact
        ⟨rowSameProvenance,
          unary_transport provenanceUnary (hsame_symm rowSameProvenance)⟩
    · intro row source
      exact ⟨provenancePkg, descentPkg, source.right, routeProvenanceDescent⟩
  exact ⟨cert, descentUnary, routeProvenanceDescent, provenancePkg, descentPkg⟩

end BEDC.Derived.ApophaticNameUp
