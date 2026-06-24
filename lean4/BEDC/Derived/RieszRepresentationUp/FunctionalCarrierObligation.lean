import BEDC.Derived.RieszRepresentationUp.TasteGate

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RieszRepresentationFunctionalCarrierObligation [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName
      sourceFunctional boundedRead functionalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg ->
      Cont source functional sourceFunctional ->
        Cont sourceFunctional ledger boundedRead ->
          Cont boundedRead boundary functionalRead ->
            PkgSig bundle functionalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row functionalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row target ∨ hsame row functional ∨
                      hsame row ledger ∨ hsame row boundary ∨ hsame row sourceFunctional ∨
                        hsame row boundedRead ∨ hsame row functionalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont source functional sourceFunctional ∧
                      Cont sourceFunctional ledger boundedRead ∧
                        Cont boundedRead boundary functionalRead ∧
                          PkgSig bundle functionalRead pkg)
                  hsame ∧
                UnaryHistory sourceFunctional ∧ UnaryHistory boundedRead ∧
                  UnaryHistory functionalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceFunctionalRoute boundedRoute functionalRoute functionalPkg
  obtain ⟨sourceUnary, _targetUnary, functionalUnary, _representingUnary, ledgerUnary,
    boundaryUnary, _provenanceUnary, _localNameUnary, _representationRoute,
    _boundaryRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have sourceFunctionalUnary : UnaryHistory sourceFunctional :=
    unary_cont_closed sourceUnary functionalUnary sourceFunctionalRoute
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed sourceFunctionalUnary ledgerUnary boundedRoute
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed boundedReadUnary boundaryUnary functionalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row functionalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row functional ∨
              hsame row ledger ∨ hsame row boundary ∨ hsame row sourceFunctional ∨
                hsame row boundedRead ∨ hsame row functionalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source functional sourceFunctional ∧
              Cont sourceFunctional ledger boundedRead ∧
                Cont boundedRead boundary functionalRead ∧ PkgSig bundle functionalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro functionalRead
        ⟨hsame_refl functionalRead, functionalReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceFunctionalRoute, boundedRoute, functionalRoute,
          functionalPkg⟩
  }
  exact ⟨cert, sourceFunctionalUnary, boundedReadUnary, functionalReadUnary⟩

end BEDC.Derived.RieszRepresentationUp
