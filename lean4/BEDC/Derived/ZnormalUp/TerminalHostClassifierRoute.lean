import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_host_classifier_route_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name classifierRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal classifierRead →
        Cont classifierRead routes rootRead →
          PkgSig bundle rootRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row terminal ∨ hsame row normal ∨ hsame row classifierRead ∨
                    hsame row rootRead)
                (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
                hsame ∧
              UnaryHistory classifierRead ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalClassifier classifierRoutesRoot rootPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalClassifier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRoot
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row normal ∨ hsame row classifierRead ∨
              hsame row rootRead)
          (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro rootRead (And.intro (hsame_refl rootRead) rootUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            And.intro (hsame_trans (hsame_symm sameRows) source.left)
              (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro row source
        exact And.intro source.left rootPkg
    }
  exact And.intro cert (And.intro classifierUnary rootUnary)

end BEDC.Derived.ZnormalUp
