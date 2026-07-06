import BEDC.Derived.TheorySelfClassifierUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_ledger_row_inversion [AskSetup] [PackageSetup]
    {G E R P A L H C Q N classifierRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg →
      Cont A L classifierRead →
        Cont classifierRead H ledgerRead →
          PkgSig bundle ledgerRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row G ∨ hsame row E ∨ hsame row R ∨ hsame row P ∨
                  hsame row A ∨ hsame row L ∨ hsame row classifierRead ∨
                    hsame row ledgerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont A L classifierRead ∧
                  Cont classifierRead H ledgerRead ∧ PkgSig bundle ledgerRead pkg)
              hsame ∧ UnaryHistory classifierRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier classifierRoute ledgerRoute ledgerPkg
  obtain ⟨_gUnary, _eUnary, _rUnary, _pUnary, aUnary, lUnary, hUnary, _cUnary,
    _qUnary, _nUnary, _generatorEqualityRoute, _recursorPurityRoute,
    _classifierCarrierRoute, _provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed aUnary lUnary classifierRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed classifierUnary hUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row E ∨ hsame row R ∨ hsame row P ∨
              hsame row A ∨ hsame row L ∨ hsame row classifierRead ∨
                hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A L classifierRead ∧
              Cont classifierRead H ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, ledgerRoute, ledgerPkg⟩
  }
  exact ⟨cert, classifierUnary, ledgerUnary⟩

theorem TheorySelfClassifier_ledger_namecert_obligations_semantic_read [AskSetup] [PackageSetup]
    {G E R P A L H C Q N read : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg →
      Cont L N read →
        PkgSig bundle read pkg →
          SemanticNameCert
              (fun row : BHist => hsame row read ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row read ∨ hsame row L ∨ hsame row N ∨ hsame row G ∨
                  hsame row E ∨ hsame row R ∨ hsame row P ∨ hsame row A)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L N read ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle read pkg)
              hsame ∧
            UnaryHistory G ∧ UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory P ∧
              UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory read ∧ Cont G E R ∧
                Cont R P A ∧ Cont A L C ∧ Cont L N read ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier ledgerRoute readPkg
  have obligations :=
    TheorySelfClassifierCarrier_namecert_obligations
      (G := G) (E := E) (R := R) (P := P) (A := A) (L := L) (H := H) (C := C)
      (Q := Q) (N := N) (read := read) (bundle := bundle) (pkg := pkg)
      carrier ledgerRoute readPkg
  obtain ⟨gUnary, eUnary, rUnary, pUnary, aUnary, lUnary, readUnary,
    generatorEqualityRoute, recursorPurityRoute, classifierRoute, ledgerRouteOb,
    provenancePkg, readPkgOb⟩ := obligations
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row read ∨ hsame row L ∨ hsame row N ∨ hsame row G ∨
              hsame row E ∨ hsame row R ∨ hsame row P ∨ hsame row A)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L N read ∧ PkgSig bundle Q pkg ∧
              PkgSig bundle read pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro read ⟨hsame_refl read, readUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerRouteOb, provenancePkg, readPkgOb⟩
  }
  exact
    ⟨cert, gUnary, eUnary, rUnary, pUnary, aUnary, lUnary, readUnary,
      generatorEqualityRoute, recursorPurityRoute, classifierRoute, ledgerRouteOb,
      provenancePkg, readPkgOb⟩

end BEDC.Derived.TheorySelfClassifierUp
