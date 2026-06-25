import BEDC.Derived.RieszRepresentationUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RieszRepresentationBanachHilbertScope [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary provenance localName banachRead
      hilbertRead measureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszRepresentationCarrier source target functional representing ledger boundary provenance
        localName bundle pkg →
      Cont source functional banachRead →
        Cont functional representing hilbertRead →
          Cont ledger boundary measureRead →
            PkgSig bundle banachRead pkg →
              PkgSig bundle hilbertRead pkg →
                PkgSig bundle measureRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row banachRead ∨ hsame row hilbertRead ∨
                          hsame row measureRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row target ∨ hsame row functional ∨
                          hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                            hsame row banachRead ∨ hsame row hilbertRead ∨
                              hsame row measureRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont source functional banachRead ∧
                          Cont functional representing hilbertRead ∧
                            Cont ledger boundary measureRead ∧ PkgSig bundle banachRead pkg ∧
                              PkgSig bundle hilbertRead pkg ∧ PkgSig bundle measureRead pkg)
                      hsame ∧
                    UnaryHistory banachRead ∧ UnaryHistory hilbertRead ∧
                      UnaryHistory measureRead := by
  -- BEDC touchpoint anchor: RieszRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows banachRoute hilbertRoute measureRoute banachPkg hilbertPkg measurePkg
  obtain ⟨sourceUnary, _targetUnary, functionalUnary, representingUnary, ledgerUnary,
    boundaryUnary, _provenanceUnary, _localNameUnary, _functionalRepresentingLedger,
    _sourceTargetBoundary, _provenancePkg, _localNamePkg⟩ := carrierRows
  have banachUnary : UnaryHistory banachRead :=
    unary_cont_closed sourceUnary functionalUnary banachRoute
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed functionalUnary representingUnary hilbertRoute
  have measureUnary : UnaryHistory measureRead :=
    unary_cont_closed ledgerUnary boundaryUnary measureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row banachRead ∨ hsame row hilbertRead ∨ hsame row measureRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row functional ∨
              hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                hsame row banachRead ∨ hsame row hilbertRead ∨ hsame row measureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source functional banachRead ∧
              Cont functional representing hilbertRead ∧ Cont ledger boundary measureRead ∧
                PkgSig bundle banachRead pkg ∧ PkgSig bundle hilbertRead pkg ∧
                  PkgSig bundle measureRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro banachRead ⟨Or.inl (hsame_refl banachRead), banachUnary⟩
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
        constructor
        · cases source.left with
          | inl banachSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) banachSame)
          | inr rest =>
              cases rest with
              | inl hilbertSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) hilbertSame))
              | inr measureSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) measureSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl banachSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl banachSame))))))
      | inr rest =>
          cases rest with
          | inl hilbertSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl hilbertSame)))))))
          | inr measureSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr measureSame)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, banachRoute, hilbertRoute, measureRoute, banachPkg, hilbertPkg,
          measurePkg⟩
  }
  exact ⟨cert, banachUnary, hilbertUnary, measureUnary⟩

end BEDC.Derived.RieszRepresentationUp
